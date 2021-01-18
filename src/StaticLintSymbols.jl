module StaticLintSymbols
using CSTParser, StaticLint, SymbolServer
using CSTParser: EXPR, headof, valof
using StaticLint: haserror, LintCodeDescriptions, collect_hints, scopeof, parentof, Binding, Scope, lint_file
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
                    root_method = StaticLint.get_root_method(v, server)
                    if root_method isa Binding
                        if root_method.val isa EXPR
                            fname = VarRef(rootstore.name, Symbol(n)) 
                            extends = fname
                            methods = MethodStore[]
                            docs = get_docs(v.val)
                            get_methods(root_method, docs, fname, rootstore, methods, server)
                            if v.type == StaticLint.CoreTypes.DataType
                                name = FakeTypeName(fname, [])
                                super = FakeTypeName(VarRef(VarRef(nothing, :Core), :Any), [])
                                types = []
                                parameters, fieldnames = get_datatype_params_fieldnames(v.val)
                                rootstore[Symbol(n)] = DataTypeStore(name, super, parameters, types, fieldnames, methods, docs, scope_exports(rootmodulescope, n))
                            else
                                rootstore[Symbol(n)] = FunctionStore(fname, methods, docs, extends, scope_exports(rootmodulescope, n))
                            end
                        else
                            @info "root_method.val isn't an EXPR"
                        end
                    else
                        @info "root_method isn't a Binding"
                    end
                else
                    rootstore[Symbol(n)] = GenericStore(VarRef(rootstore.name, Symbol(n)), FakeTypeName(Any), get_docs(v.val), scope_exports(rootmodulescope, n))
                end
            end
        end
    end
    rootstore
end

function get_methods(root_method, docs, fname, rootstore, methods, server)
    while root_method isa Binding
        file, line = get_filename_line(root_method.val, server)
        
        sig = []
        kws = Symbol[]
        docs1 = get_docs(root_method.val)
        if !isempty(docs1)
            docs = string(docs, "\n", docs1)
        end
        rt =VarRef(VarRef(nothing, :Core), :Any)
        push!(methods, MethodStore(fname.name, rootstore.name.name, file, line, sig, kws, rt))
        root_method = root_method.next
    end
    docs, methods
end

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
    for (n, b) in scopeof(x).names
        if StaticLint.is_in_fexpr(b.val, x-> x == sig)
            lb, ub = get_typevar_bounds(b.val)
            push!(params, FakeTypeVar(Symbol(n), lb, ub))
        else
            push!(fns, Symbol(n))
        end
    end
    params, fns
end

end # module
