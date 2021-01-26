module StaticLintSymbols
using CSTParser, StaticLint, SymbolServer
using CSTParser: EXPR, headof, valof
using StaticLint: haserror, LintCodeDescriptions, collect_hints, scopeof, parentof, Binding, Scope, lint_file, bindingof, hasbinding
using SymbolServer: VarRef, ModuleStore, FunctionStore, MethodStore, DataTypeStore, GenericStore, FakeTypeName, FakeTypeofBottom, FakeTypeofVararg, FakeTypeVar, FakeUnion, FakeUnionAll

# From StaticLint, modififed.
function scope_exports(scope::Scope, name::String)
    if StaticLint.scopehasbinding(scope, name) && (b = scope.names[name]) isa Binding
        for ref in b.refs
            if ref isa EXPR && parentof(ref) isa EXPR && headof(parentof(ref)) === :export
                return true
            end
        end
    end
    return false
end

function symbols(pkg_dir::String, server = StaticLint.FileServer())
    pkg_name = last(splitpath(pkg_dir))
    rootpath = joinpath(pkg_dir, "src", "$(pkg_name).jl")
    isfile(rootpath) || @info "$pkg_dir isn't "
    root = lint_file(rootpath, server)
    (scopeof(root.cst) isa StaticLint.Scope && haskey(scopeof(root.cst).names, pkg_name) && 
        scopeof(root.cst).names[pkg_name] isa StaticLint.Binding && scopeof(root.cst).names[pkg_name].val isa CSTParser.EXPR&&
        CSTParser.defines_module(scopeof(root.cst).names[pkg_name].val)) || 
        @info "No matching module found in $rootpath"
    
    rootstore = symbols(scopeof(root.cst).names[pkg_name].val, server)
    rootstore
end

function get_docs(x::EXPR)
    ""
end

function count_lines(str, offset)
    cus = codeunits(str)
    i, cnt = 1, 1
    while i <= offset
        if cus[i] == 0x0a
            cnt += 1
        end
        i += 1 
    end
    cnt
end

function get_filename_line(x, server, offset = 0)
    if parentof(x) isa EXPR
        for a in parentof(x)
            x == a && return get_filename_line(parentof(x), server, offset)
            offset += a.fullspan
        end
    elseif headof(x) === :file
        for (p, f) in server.files
            if f.cst == x
                return p, count_lines(f.source, offset)
            end
        end
        @info "Couldn't find filename"
        return "", 0
    else
        @info "Couldn't find :file parent"
        return "", 0
    end
end

function symbols(expr::EXPR, server, pkg_name = CSTParser.get_name(expr).val, rootstore = ModuleStore(VarRef(nothing, Symbol(pkg_name)), Dict(), "", true, [], []))
    rootmodulescope = scopeof(expr)
    for (n, v) in rootmodulescope.names
        # .used modules
        if v isa VarRef
            
        elseif v isa Binding
            if v.val isa EXPR
                if CSTParser.defines_module(v.val)
                    name = (valof(CSTParser.get_name(v.val))) 
                    if name == pkg_name 
                        rootstore[Symbol(n)] = rootstore.name
                    else
                        rootstore[Symbol(n)] = symbols(v.val, server, n, ModuleStore(VarRef(rootstore.name, Symbol(name)), Dict(), get_docs(v.val), true, [], []))
                    end
                elseif v.type == StaticLint.CoreTypes.Function || v.type == StaticLint.CoreTypes.DataType
                    fname = VarRef(rootstore.name, Symbol(n)) 
                    extends = fname
                    methods = MethodStore[]
                    docs = get_docs(v.val)
                    for ref in v.refs 
                        method = StaticLint.get_method(ref)
                        if method !== nothing
                            if method isa EXPR
                                file, line = get_filename_line(method, server)
                                sig, kws = get_method_sig(method)
                                docs1 = get_docs(method)
                                if !isempty(docs1)
                                    docs = string(docs, "\n", docs1)
                                end
                                rt = VarRef(VarRef(nothing, :Core), :Any)
                                push!(methods, MethodStore(fname.name, rootstore.name.name, file, line, sig, kws, rt))
                            end
                        end
                    end
                    if v.type == StaticLint.CoreTypes.DataType
                        name = FakeTypeName(fname, [])
                        super = FakeTypeName(VarRef(VarRef(nothing, :Core), :Any), [])
                        parameters, fieldnames, types = scopeof(v.val) === nothing ? ([], [], []) : get_datatype_params_fieldnames(v.val)
                        rootstore[Symbol(n)] = DataTypeStore(name, super, parameters, types, fieldnames, methods, docs, scope_exports(rootmodulescope, n))
                    else
                        rootstore[Symbol(n)] = FunctionStore(fname, methods, docs, extends, scope_exports(rootmodulescope, n))
                    end
                else
                    n == "WS" && @info v.type
                    rootstore[Symbol(n)] = GenericStore(VarRef(rootstore.name, Symbol(n)), FakeTypeName(Any), get_docs(v.val), scope_exports(rootmodulescope, n))
                end
            end
        end
    end
    rootstore
end

function get_method_sig(x::EXPR)
    args = []
    kws = []
    if CSTParser.defines_function(x)
        sig = CSTParser.rem_wheres_decls(CSTParser.get_sig(x))
        if sig.head === :call
            for i = 2:length(sig.args)
                a = sig.args[i]
                if headof(a) === :parameters
                    for p in a.args
                        b = get_binding_from_expr(p)
                        b isa Binding && CSTParser.isidentifier(b.name) && push!(kws, Symbol(valof(b.val)))
                    end
                else
                    # TODO: add multiple methods if we encounter kw args
                    b = get_binding_from_expr(a)
                    b isa Binding && CSTParser.isidentifier(b.name) && push!(args, Symbol(valof(b.name)) => get_type_from_binding(b))
                end
            end
        end
    elseif CSTParser.defines_struct(x)
        if !any(CSTParser.defines_function, x.args[3].args)
            for a in x.args[3].args
                b = get_binding_from_expr(a)
                b isa Binding && CSTParser.isidentifier(b.name) && push!(args, Symbol(valof(b.name)) => get_type_from_binding(b))
            end
        end
    end 
    args, kws
end
CSTParser.rem_wheres_decls
function get_typevar_bounds(x::EXPR)
    # Just assumes `z <: Any` for now
    lb = FakeTypeofBottom()
    ub = FakeTypeName(VarRef(VarRef(nothing, :Core), :Any), [])
    return lb, ub
end

function get_datatype_params_fieldnames(x::EXPR)
    sig = CSTParser.get_sig(x)
    params = []
    fns = []
    fntypes = []
    scopeof(x) === nothing && @info x
    for (n, b) in scopeof(x).names
        if StaticLint.is_in_fexpr(b.val, x-> x == sig)
            lb, ub = get_typevar_bounds(b.val)
            push!(params, FakeTypeVar(Symbol(n), lb, ub))
        else
            push!(fns, Symbol(n))
            push!(fntypes, get_type_from_binding(b))
        end
    end
    params, fns, fntypes
end

function get_type_from_binding(b)
    if b.type isa SymbolServer.DataTypeStore
        b.type.name
    elseif b.type isa Binding && b.type.val isa EXPR
        FakeTypeName(getVarRef(b.type), [])
    elseif b.type isa Binding && b.type.val isa SymbolServer.DataTypeStore
        b.type.val.name
    else
        FakeTypeName(VarRef(VarRef(nothing, :Core), :Any), [])
    end
end

function getVarRef(b::Binding, s = StaticLint.retrieve_scope(b.val), names = [Symbol(valof(b.name))])
    s.parent === nothing && return reduce((a,b) -> VarRef(a,b), reverse(names), init = nothing)
    if CSTParser.defines_module(s.expr)
        push!(names, Symbol(valof(CSTParser.get_name(s.expr))))
    end
    return getVarRef(b, StaticLint.retrieve_toplevel_scope(s.parent), names)
end

function get_binding_from_expr(x::EXPR)
    if hasbinding(x)
        return bindingof(x)
    end
    for a in x
        r = get_binding_from_expr(a)
        r !== nothing && return r
    end
    return
end


function comp(d1::ModuleStore, d2::ModuleStore)
    for k in union(keys(d1.vals), keys(d1.vals))
        if haskey(d1.vals, k) && haskey(d2.vals, k)
            comp(d1[k], d2[k]) || @info "Generic store $(d1.name).$k"
        elseif startswith(String(k), "#")
        elseif !haskey(d2.vals, k)
            # @info "d2 missing $(d1.name).$k"
        end
    end
    true
end
function comp(d1::GenericStore, d2::GenericStore)
    d1.name == d2.name && d1.doc == d2.doc && d1.typ == d2.typ && d1.exported == d2.exported
end

comp(d1, d2) = true

end # module
