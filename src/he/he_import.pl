:- dynamic module_mount/2.
:- dynamic loaded_module_record/4.
:- dynamic imported_file_into/2.

term_atom_string(Term, String) :-
    string(Term), !,
    String = Term.
term_atom_string(Term, String) :-
    atom(Term),
    atom_string(Term, String).

he_is_absolute_path_string(S) :-
    atom_string(A, S),
    is_absolute_file_name(A).

ancestor_dir(Dir, Dir).
ancestor_dir(Dir, Ancestor) :-
    file_directory_name(Dir, Parent),
    Parent \== Dir,
    ancestor_dir(Parent, Ancestor).

current_import_base(Base) :-
    working_dir(Base), !.
current_import_base(Base) :-
    working_directory(Base, Base).

resolve_existing_dir(Spec, Dir) :-
    current_import_base(Base),
    ancestor_dir(Base, Ancestor),
    directory_file_path(Ancestor, Spec, Candidate),
    exists_directory(Candidate), !,
    absolute_file_name(Candidate, Dir).

resolve_existing_file(Spec, Path) :-
    current_import_base(Base),
    resolve_existing_file_from_base(Base, Spec, Path).

resolve_existing_file_from_base(Base, Spec, Path) :-
    ancestor_dir(Base, Ancestor),
    resolve_existing_file_candidate(Ancestor, Spec, Path), !.
resolve_existing_file_from_base(Base, Spec, Path) :-
    sub_string(Spec, 0, 6, _, "tests/"),
    sub_string(Spec, 6, _, 0, Short),
    ancestor_dir(Base, Ancestor),
    resolve_existing_file_candidate(Ancestor, Short, Path), !.

resolve_existing_file_candidate(Base, Spec, Path) :-
    directory_file_path(Base, Spec, Candidate0),
    ensure_metta_ext(Candidate0, Candidate),
    exists_file(Candidate), !,
    absolute_file_name(Candidate, Path).

resolve_existing_data_file(Spec, Path) :-
    current_import_base(Base),
    resolve_existing_data_file_from_base(Base, Spec, Path), !.
resolve_existing_data_file(Spec, Path) :-
    working_directory(Base, Base),
    resolve_existing_data_file_from_base(Base, Spec, Path), !.

resolve_existing_data_file_from_base(Base, Spec, Path) :-
    ancestor_dir(Base, Ancestor),
    directory_file_path(Ancestor, Spec, Candidate),
    exists_file(Candidate), !,
    absolute_file_name(Candidate, Path).
resolve_existing_data_file_from_base(Base, Spec, Path) :-
    sub_string(Spec, 0, 6, _, "tests/"),
    sub_string(Spec, 6, _, 0, Short),
    ancestor_dir(Base, Ancestor),
    directory_file_path(Ancestor, Short, Candidate),
    exists_file(Candidate), !,
    absolute_file_name(Candidate, Path).

module_name_from_dir(Dir, Name) :-
    file_base_name(Dir, Base),
    atom_string(Name, Base).

module_spec_path(Spec, Display, Path, 'registered-root') :-
    term_atom_string(Spec, SpecString),
    split_string(SpecString, ":", "", [RootString|Rest]),
    Rest \= [], !,
    atom_string(Root, RootString),
    module_mount(Root, RootDir),
    atomic_list_concat(Rest, '/', RelAtom),
    atom_string(RelAtom, Rel),
    resolve_existing_file_from_base(RootDir, Rel, Path),
    Display = SpecString.
module_spec_path(Spec, Display, Path, 'relative-file') :-
    term_atom_string(Spec, SpecString),
    resolve_existing_file(SpecString, Path),
    Display = SpecString.

'register-module!'(Spec, true) :-
    term_atom_string(Spec, SpecString),
    resolve_existing_dir(SpecString, Dir),
    module_name_from_dir(Dir, Name),
    retractall(module_mount(Name, _)),
    assertz(module_mount(Name, Dir)).

import_loaded_module(Space, Display, Path, Provider) :-
    ( imported_file_into(Path, Space)
    -> true
    ; assertz(imported_file_into(Path, Space)),
      load_metta_file(Path, _, Space)
    ),
    ( loaded_module_record(Display, Path, Provider, _)
    -> true
    ; assertz(loaded_module_record(Display, Path, Provider, Space)) ).

'mod-space!'(Spec, Space) :-
    module_spec_path(Spec, Display, Path, Provider),
    flag(metta_module_space_id, Id0, Id0 + 1),
    Id is Id0 + 1,
    format(atom(Space), '&module_~d', [Id]),
    import_loaded_module(Space, Display, Path, Provider).

add_module_inventory_fact(Space, Fact) :-
    ( once(match(Space, Fact, Fact, _))
    -> true
    ; add_sexp(Space, Fact)
    ).

install_he_library("str") :-
    register_he_compat_helper('str-length', 2),
    register_he_compat_helper('str-split-whitespace', 2),
    register_he_compat_helper('str-trim', 2).
install_he_library("fs") :-
    register_he_compat_helper('fs-exists?', 2),
    register_he_compat_helper('fs-read-lines', 2).
install_he_library("system") :-
    register_he_compat_helper('system-cwd', 1),
    register_he_compat_helper('system-has-args', 1).

'module-inventory!'(Space) :-
    flag(metta_module_inventory_id, Id0, Id0 + 1),
    Id is Id0 + 1,
    format(atom(Space), '&module_inventory_~d', [Id]),
    add_module_inventory_fact(Space, ['module-profile', he]),
    add_module_inventory_fact(Space, ['module-provider', 'registered-root', enabled]),
    add_module_inventory_fact(Space, ['module-provider', 'relative-file', enabled]),
    add_module_inventory_fact(Space, ['module-provider', 'git-remote', enabled]),
    add_module_inventory_fact(Space, ['module-provider-implementation', 'registered-root', implemented]),
    add_module_inventory_fact(Space, ['module-provider-implementation', 'git-remote', implemented]),
    add_module_inventory_fact(Space, ['module-provider-transport', 'registered-root', local]),
    add_module_inventory_fact(Space, ['module-provider-transport', 'git-remote', remote]),
    add_module_inventory_fact(Space, ['module-provider-cache-policy', 'registered-root', 'no-cache']),
    add_module_inventory_fact(Space, ['module-provider-cache-policy', 'git-remote', 'cache-backed']),
    add_module_inventory_fact(Space, ['module-provider-locator-kind', 'registered-root', 'filesystem-path']),
    add_module_inventory_fact(Space, ['module-provider-locator-kind', 'git-remote', 'git-url']),
    add_module_inventory_fact(Space, ['module-provider-update-policy', 'registered-root', 'manual-register']),
    add_module_inventory_fact(Space, ['module-provider-update-policy', 'git-remote', 'try-fetch-latest']),
    add_module_inventory_fact(Space, ['module-provider-revision-policy', 'registered-root', none]),
    add_module_inventory_fact(Space, ['module-provider-revision-policy', 'git-remote', 'default-branch-only']),
    forall(module_mount(Name, Root),
           ( add_module_inventory_fact(Space, ['module-mount', Name, Root, 'registered-root']),
             add_module_inventory_fact(Space, ['module-mount-source', Name, Root, 'filesystem-path']),
             add_module_inventory_fact(Space, ['module-mount-revision-policy', Name, none, "none"]) )),
    forall(loaded_module_record(Display, Path, Provider, LoadedSpace),
           ( add_module_inventory_fact(Space, ['loaded-module', Display, Path, Provider]),
             add_module_inventory_fact(Space, ['loaded-module-space', Display, LoadedSpace, Provider]) )).

importer_helper(_, mork) :- !.
importer_helper(_, File) :-
    he_profile_enabled,
    ( atom(File) ; string(File) ),
    term_atom_string(File, LibName),
    install_he_library(LibName), !.
importer_helper(Space, [library, Name]) :-
    term_atom_string(Name, LibName),
    ( install_he_library(LibName)
    -> true
    ; atomic_list_concat(['lib/', LibName], RelAtom),
      atom_string(RelAtom, Rel),
      resolve_existing_file(Rel, Path),
      import_loaded_module(Space, LibName, Path, 'relative-file')
    ), !.
importer_helper(Space, File) :-
    module_spec_path(File, Display, PathWithExt, Provider), !,
    import_loaded_module(Space, Display, PathWithExt, Provider).
importer_helper(Space, File) :-
    atom_string(File, SFile),
    ( file_name_extension(ModPath, 'py', SFile)
    -> current_import_base(Base),
       absolute_file_name(SFile, Path, [relative_to(Base)]),
       file_directory_name(Path, Dir),
       file_base_name(ModPath, ModuleName),
       py_call(sys:path:append(Dir), _),
       py_call(builtins:'__import__'(ModuleName), _)
    ; resolve_existing_file(SFile, PathWithExt), !,
      import_loaded_module(Space, SFile, PathWithExt, 'relative-file')
    ).
