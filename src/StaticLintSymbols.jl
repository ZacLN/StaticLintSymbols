module StaticLintSymbols
using CSTParser, StaticLint, SymbolServer
using CSTParser: EXPR, headof, valof
using StaticLint: haserror, LintCodeDescriptions, collect_hints, scopeof, parentof, Binding, Scope
using SymbolServer: VarRef, ModuleStore, FunctionStore, MethodStore, DataTypeStore, GenericStore, FakeTypeName
function setup_server(env = dirname(SymbolServer.Pkg.Types.Context().env.project_file), depot = first(SymbolServer.Pkg.depots()), cache = joinpath(dirname(pathof(SymbolServer)), "..", "store"))
    server = StaticLint.FileServer()
    ssi = SymbolServerInstance(depot, cache)
    _, server.symbolserver = SymbolServer.getstore(ssi, env)
    server.symbol_extends  = SymbolServer.collect_extended_methods(server.symbolserver)
    server
end

"""
    lint_string(s, server; gethints = false)
Parse a string and run a semantic pass over it. This will mark scopes, bindings,
references, and lint hints. An annotated `EXPR` is returned or, if `gethints = true`,
it is paired with a collected list of errors/hints.
"""
function lint_string(s::String, server = setup_server(); gethints = false)
    empty!(server.files)
    f = StaticLint.File("", s, CSTParser.parse(s, true), nothing, server)
    StaticLint.setroot(f, f)
    StaticLint.setfile(server, "", f)
    StaticLint.semantic_pass(f)
    StaticLint.check_all(f.cst, StaticLint.LintOptions(), server)
    if gethints
        return f.cst, [(x, string(haserror(x) ? LintCodeDescriptions[x.meta.error] : "Missing reference", " at offset ", offset)) for (offset, x) in collect_hints(f.cst, server)]
    else
        return f.cst
    end
end

"""
    lint_file(rootpath, server)
Read a file from disc, parse and run a semantic pass over it. The file should be the 
root of a project, e.g. for this package that file is `src/StaticLint.jl`. Other files
in the project will be loaded automatically (calls to `include` with complicated arguments
are not handled, see `followinclude` for details). A `FileServer` will be returned 
containing the `File`s of the package.
"""
function lint_file(rootpath, server = setup_server(); gethints = false)
    empty!(server.files)
    root = StaticLint.loadfile(server, rootpath)
    StaticLint.semantic_pass(root)
    for (p,f) in server.files
        StaticLint.check_all(f.cst, StaticLint.LintOptions(), server)
    end
    if gethints
        hints = []
        for (p,f) in server.files
            append!(hints, [(x, string(haserror(x) ? LintCodeDescriptions[x.meta.error] : "Missing reference", " at offset ", offset, " of ", p)) for (offset, x) in collect_hints(f.cst, server)])
        end
        return root, hints
    else
        return root
    end
end

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
    
    rootstore = symbols(scopeof(root.cst).names[pkg_name].val)
    rootstore
end

function get_docs(x::EXPR)
    ""
end

function symbols(expr, server, pkg_name = CSTParser.get_name(expr).val, rootstore = ModuleStore(VarRef(nothing, Symbol(pkg_name)), Dict(), "", true, [], []))
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
                elseif v.type == StaticLint.CoreTypes.Function
                    root_method = StaticLint.get_root_method(v, server)
                    if root_method isa Binding
                        if root_method.val isa EXPR
                            fname = VarRef(rootstore.name, Symbol(n)) 
                            extends = fname
                            methods = MethodStore[]
                            docs = get_docs(v.val)
                            while root_method isa Binding
                                file = ""
                                line = 0
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
                            rootstore[Symbol(n)] = FunctionStore(fname, [], docs, extends, scope_exports(rootmodulescope, n))
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

end # module
