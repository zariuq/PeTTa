:- dynamic module_mount/2.
:- dynamic loaded_module_record/4.
:- dynamic imported_file_into/2.
:- dynamic import_loading_into/3.

he_space_snapshot_atoms(Space, Atoms) :-
    findall(Atom, 'get-atoms'(Space, Atom), Atoms).

he_restore_space_atoms(Space, Atoms) :-
    he_space_snapshot_atoms(Space, Current),
    forall(member(Atom, Current), 'remove-atom'(Space, Atom, _)),
    forall(member(Atom, Atoms), 'add-atom'(Space, Atom, _)).

he_import_error_result(Result, Error) :-
    Result = ['Error'|_], !,
    Error = Result.
he_import_error_result(Result, Error) :-
    is_list(Result),
    member(Item, Result),
    he_import_error_result(Item, Error), !.

he_import_runtime_error(Results, Error) :-
    member(Result, Results),
    he_import_error_result(Result, Error), !.

he_direct_module_term(parsed(function, _, Term), Term).
he_direct_module_term(parsed(expression, _, Term), Term).

he_equation_term([=|_]).
he_type_decl_term([':'|_]).

he_module_visible_import_fact(Term) :-
    nonvar(Term),
    \+ he_equation_term(Term),
    \+ he_type_decl_term(Term),
    \+ ( atom(Term),
         he_space_type(Term, _)
       ).

he_sort_module_export_atoms(Terms, Sorted) :-
    include(he_equation_term, Terms, Equations),
    exclude(he_equation_term, Terms, Others),
    append(Equations, Others, Ordered),
    alpha_list_to_set(Ordered, Sorted).

he_module_direct_export_atoms(Path, Atoms) :-
    read_file_to_string(Path, Source, []),
    string_codes(Source, RawCodes),
    strip(RawCodes, 0, Codes),
    phrase(top_forms(Forms, 1), Codes),
    maplist(parse_form, Forms, ParsedForms),
    findall(Term,
            ( member(Parsed, ParsedForms),
              he_direct_module_term(Parsed, Term)
            ),
            Terms0),
    he_sort_module_export_atoms(Terms0, Atoms).

he_trim_imported_space_to_direct_exports('&self', _Path, _Snapshot) :- !.
he_trim_imported_space_to_direct_exports(Space, Path, Snapshot) :-
    he_module_direct_export_atoms(Path, DirectAtoms),
    he_space_snapshot_atoms(Space, LoadedAtoms),
    include(he_module_visible_import_fact, LoadedAtoms, VisibleImportFacts),
    append(Snapshot, DirectAtoms, Combined1),
    append(Combined1, VisibleImportFacts, Combined0),
    alpha_list_to_set(Combined0, Combined),
    he_replace_space_atoms(Space, Combined).

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
    resolve_existing_dir_from_base(Base, Spec, Dir), !.

resolve_existing_dir_from_base(Base, Spec, Dir) :-
    ancestor_dir(Base, Ancestor),
    directory_file_path(Ancestor, Spec, Candidate),
    exists_directory(Candidate), !,
    absolute_file_name(Candidate, Dir).
resolve_existing_dir_from_base(Base, Spec, Dir) :-
    legacy_cetta_support_spec(Spec),
    ancestor_dir(Base, Ancestor),
    legacy_cetta_tests_dir(RelDir),
    directory_file_path(Ancestor, RelDir, TestsDir),
    directory_file_path(TestsDir, Spec, Candidate),
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
    absolute_data_file_path(Spec, Path), !.
resolve_existing_data_file(Spec, Path) :-
    current_import_base(Base),
    resolve_existing_data_file_from_base(Base, Spec, Path), !.
resolve_existing_data_file(Spec, Path) :-
    working_directory(Base, Base),
    resolve_existing_data_file_from_base(Base, Spec, Path), !.

absolute_data_file_path(Spec, Path) :-
    atom(Spec),
    is_absolute_file_name(Spec),
    exists_file(Spec), !,
    absolute_file_name(Spec, Path).
absolute_data_file_path(Spec, Path) :-
    he_is_absolute_path_string(Spec),
    atom_string(SpecAtom, Spec),
    is_absolute_file_name(SpecAtom),
    exists_file(SpecAtom), !,
    absolute_file_name(SpecAtom, Path).

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
resolve_existing_data_file_from_base(Base, Spec, Path) :-
    resolve_legacy_metamath_fixture(Base, Spec, Path), !.

resolve_legacy_metamath_fixture(Base, Spec, Path) :-
    legacy_metamath_fixture_rel_root(RelRoot),
    sub_string(Spec, _, _, _, RelRoot),
    file_base_name(Spec, BaseName),
    ancestor_dir(Base, Ancestor),
    legacy_metamath_fixture_dir(RelDir),
    directory_file_path(Ancestor, RelDir, Dir),
    directory_file_path(Dir, BaseName, Candidate),
    exists_file(Candidate), !,
    absolute_file_name(Candidate, Path).

legacy_metamath_fixture_rel_root("metamath-test/tests/core/small/").

legacy_metamath_fixture_dir("hyperon/CeTTa/tests/support/metamath/core/small").
legacy_metamath_fixture_dir("hyperon/CeTTa-main-test/tests/support/metamath/core/small").
legacy_metamath_fixture_dir("hyperon/CeTTa-promote/tests/support/metamath/core/small").
legacy_metamath_fixture_dir("hyperon/petta-he-profile/tests/support/metamath/core/small").

module_name_from_dir(Dir, Name) :-
    file_base_name(Dir, Base),
    atom_string(Name, Base).

legacy_cetta_support_spec(Spec) :-
    sub_string(Spec, 0, 8, _, "support/"), !.
legacy_cetta_support_spec(Spec) :-
    sub_string(Spec, 0, 12, _, "support_alt/").

legacy_cetta_tests_dir("hyperon/CeTTa/tests").
legacy_cetta_tests_dir("hyperon/CeTTa-main-test/tests").
legacy_cetta_tests_dir("hyperon/CeTTa-promote/tests").

split_registered_module_spec(SpecString, RootString, Rest) :-
    split_string(SpecString, ":", "", [RootString|Rest]),
    Rest \= [], !.
split_registered_module_spec(SpecString, RootString, Rest) :-
    \+ sub_string(SpecString, _, _, _, "/"),
    \+ sub_string(SpecString, _, _, _, ":"),
    split_string(SpecString, ".", "", [RootString|Rest]),
    Rest \= [].

module_spec_path(Spec, Display, Path, 'registered-root') :-
    term_atom_string(Spec, SpecString),
    split_registered_module_spec(SpecString, RootString, Rest), !,
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
module_spec_path(Spec, Display, Path, 'stdlib-file') :-
    term_atom_string(Spec, SpecString),
    atomic_list_concat(['lib', SpecString], '/', RelAtom),
    atom_string(RelAtom, Rel),
    resolve_existing_file(Rel, Path),
    Display = SpecString.

'register-module!'(Spec, []) :-
    term_atom_string(Spec, SpecString),
    resolve_existing_dir(SpecString, Dir),
    module_name_from_dir(Dir, Name),
    retractall(module_mount(Name, _)),
    assertz(module_mount(Name, Dir)).

import_loaded_module_low_level(Space, Display, Path, Provider) :-
    ( imported_file_into(Path, Space)
    -> true
    ; assertz(imported_file_into(Path, Space)),
      load_metta_file(Path, _, Space)
    ),
    ( loaded_module_record(Display, Path, Provider, _)
    -> true
    ; assertz(loaded_module_record(Display, Path, Provider, Space)) ).

he_import_target('&self', '&self', existing) :- !.
he_import_target(SpaceRef, Space, existing) :-
    he_resolve_space_ref(SpaceRef, Space),
    Space \== SpaceRef, !.
he_import_target(SpaceRef, SpaceRef, existing) :-
    atom(SpaceRef),
    he_space_type(SpaceRef, _), !.
he_import_target(SpaceRef, Space, fresh_bind(SpaceRef, Space)) :-
    he_space_ref_atom(SpaceRef),
    'new-space'(Space).

he_import_success_bind(existing) :- !.
he_import_success_bind(fresh_bind(SpaceRef, Space)) :-
    nb_setval(SpaceRef, Space).

he_import_failure_cleanup(existing, Space, Snapshot, Path) :-
    he_restore_space_atoms(Space, Snapshot),
    retractall(imported_file_into(Path, Space)).
he_import_failure_cleanup(fresh_bind(_SpaceRef, Space), _Space, _Snapshot, Path) :-
    retractall(imported_file_into(Path, Space)),
    he_restore_space_atoms(Space, []),
    retractall(he_space_type(Space, _)).

he_import_mm2_error(Display, ['ModuleMm2LoadFailed', Display,
                              "generic import/include does not accept .mm2; use (mork:include! <MorkSpace> spec)"]) :-
    sub_string(Display, _, 4, 0, ".mm2").

he_import_cycle_error(Path, Display, ['ModuleImportCycle', CycleDisplay]) :-
    ( import_loading_into(Path, _, CycleDisplay0)
    -> CycleDisplay = CycleDisplay0
    ;  CycleDisplay = Display
    ).

he_import_load_status(Display, Path, Space, Status) :-
    ( he_import_mm2_error(Display, Error)
    -> Status = error(Error)
    ; catch(load_metta_file(Path, Results, Space), _,
            Status = error(['ModuleParseFailed', Display]))
    -> ( var(Status)
       -> ( he_import_runtime_error(Results, Error)
          -> Status = error(Error)
          ;  Status = ok
          )
       ;  true
       )
    ; Status = error(['ModuleParseFailed', Display])
    ).

he_import_common(Surface, SpaceRef, File, SuccessOut, Out) :-
    module_spec_path(File, Display, Path, Provider),
    he_import_target(SpaceRef, Space, Mode),
    he_space_snapshot_atoms(Space, Snapshot),
    ( imported_file_into(Path, Space)
    -> he_import_success_bind(Mode),
       Out = SuccessOut
    ; he_import_cycle_error(Path, Display, Error),
      import_loading_into(Path, Space, _),
      he_import_failure_cleanup(Mode, Space, Snapshot, Path),
      Out = ['Error', [Surface, SpaceRef, File], Error]
    ; setup_call_cleanup(
          assertz(import_loading_into(Path, Space, Display)),
          ( he_import_load_status(Display, Path, Space, Status),
            ( Status == ok
          -> he_trim_imported_space_to_direct_exports(Space, Path, Snapshot),
             assertz(imported_file_into(Path, Space)),
             ( loaded_module_record(Display, Path, Provider, _)
             -> true
             ; assertz(loaded_module_record(Display, Path, Provider, Space))
             ),
             he_import_success_bind(Mode),
             Out = SuccessOut
          ; Status = error(Error),
            he_import_failure_cleanup(Mode, Space, Snapshot, Path),
            Out = ['Error', [Surface, SpaceRef, File], Error]
            )
          ),
          retractall(import_loading_into(Path, Space, Display)))
    ).

he_builtin_he_import(mork) :- !.
he_builtin_he_import(File) :-
    ( atom(File) ; string(File) ),
    term_atom_string(File, LibName),
    install_he_library(LibName).

he_import_surface(_SpaceRef, File, Out) :-
    he_builtin_he_import(File), !,
    Out = [].
he_import_surface(SpaceRef, File, Out) :-
    once(he_import_common('import!', SpaceRef, File, [], Out)),
    ( Out = ['Error'|_]
    -> true
    ; module_spec_path(File, Display, Path, Provider),
      he_resolve_space_ref(SpaceRef, LoadedSpace),
      ( loaded_module_record(Display, Path, Provider, _)
      -> true
      ; assertz(loaded_module_record(Display, Path, Provider, LoadedSpace))
      )
    ).

he_include_surface(SpaceRef, File, Out) :-
    once(he_import_common(include, SpaceRef, File, [], Out)).

'mod-space!'(Spec, Space) :-
    module_spec_path(Spec, Display, Path, Provider),
    flag(metta_module_space_id, Id0, Id0 + 1),
    Id is Id0 + 1,
    format(atom(Space), '&module_~d', [Id]),
    ( he_space_type(Space, _) -> true ; assertz(he_space_type(Space, 'Space')) ),
    import_loaded_module_low_level(Space, Display, Path, Provider).

add_module_inventory_fact(Space, Fact) :-
    ( once(match(Space, Fact, Fact, _))
    -> true
    ; add_sexp(Space, Fact),
      he_note_space_fact_added(Space, Fact)
    ).

install_he_library("str") :-
    register_he_compat_helper('str-length', 2),
    register_he_compat_helper('str-concat', 3),
    register_he_compat_helper('str-split', 3),
    register_he_compat_helper('str-split-whitespace', 2),
    register_he_compat_helper('str-join', 3),
    register_he_compat_helper('str-slice', 4),
    register_he_compat_helper('str-find', 3),
    register_he_compat_helper('str-starts-with?', 3),
    register_he_compat_helper('str-ends-with?', 3),
    register_he_compat_helper('str-trim', 2).
install_he_library("fs") :-
    register_he_compat_helper('fs-exists?', 2),
    register_he_compat_helper('fs-read-lines', 2),
    register_he_compat_helper('fs-read-text', 2),
    register_he_compat_helper('fs-resolve-path', 2).
install_he_library("system") :-
    register_he_compat_helper('system-cwd', 1),
    register_he_compat_helper('system-has-args', 1).

'module-inventory!'(Space) :-
    flag(metta_module_inventory_id, Id0, Id0 + 1),
    Id is Id0 + 1,
    format(atom(Space), '&module_inventory_~d', [Id]),
    ( he_space_type(Space, _) -> true ; assertz(he_space_type(Space, 'Space')) ),
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
      import_loaded_module_low_level(Space, LibName, Path, 'relative-file')
    ), !.
importer_helper(Space, File) :-
    module_spec_path(File, Display, PathWithExt, Provider), !,
    import_loaded_module_low_level(Space, Display, PathWithExt, Provider).
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
      import_loaded_module_low_level(Space, SFile, PathWithExt, 'relative-file')
    ).
