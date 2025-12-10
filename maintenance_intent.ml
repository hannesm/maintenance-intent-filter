
let ocaml_versions = [
  "4.08.1"; "4.09.1"; "4.10.2"; "4.11.2"; "4.12.1"; "4.13.1"; "4.14.2";
  "5.0.0"; "5.1.1"; "5.2.1"; "5.3.0"; "5.4.0"
]

module S = Set.Make(String)
module M = Map.Make(String)

let package s =
  let dot = String.index s '.' in
  String.sub s 0 dot

let version s =
  let dot = succ (String.index s '.') in
  String.sub s dot (String.length s - dot)

let env =
  Opam_0install.Dir_context.std_env
    ~arch:"x86_64"
    ~os:"linux"
    ~os_family:"debian"
    ~os_distribution:"debian"
    ~os_version:"10"
    ()

let context ?(constraints = []) dir compiler_version =
  let constraints =
    OpamPackage.Name.Map.of_list
      ((OpamPackage.Name.of_string "ocaml",
        (`Eq, OpamPackage.Version.of_string compiler_version)) :: constraints)
  in
  Opam_0install.Dir_context.create (dir ^ "/packages") ~constraints ~env

module Solver = Opam_0install.Solver.Make(Opam_0install.Dir_context)

let solve ~retain_all context package =
  let pkg = OpamPackage.Name.of_string package in
  let result = Solver.solve context [ pkg ] in
  match result with
  | Error e -> Error (Solver.diagnostics e)
  | Ok selections ->
    let pkgs = Solver.packages_of_result selections in
    if retain_all then
      Ok pkgs
    else
      Ok [ List.find (fun p -> OpamPackage.Name.equal (OpamPackage.name p) pkg)
            pkgs ]

let solve_by_ocaml_version ?(retain_all = false) contexts package_name =
  let to_keep =
    List.fold_left2 (fun acc context ocaml_version ->
        match solve ~retain_all context package_name with
        | Ok pkgs -> S.union (S.of_list (List.map OpamPackage.to_string pkgs)) acc
        | Error _ -> Logs.info (fun m -> m "%s for ocaml %s got no solution" package_name ocaml_version); acc)
      S.empty contexts ocaml_versions
  in
  (*Logs.app (fun m -> m "0install keeping %a" Fmt.(list ~sep:(any ", ") string)
               (S.elements to_keep));*)
  to_keep

let pkg_name_and_version path =
  match List.rev (Fpath.segs path) with
  | _opam :: pkg_ver :: pkg :: _rest -> pkg, pkg_ver
  | _ -> assert false

let not_maintained (_, opam) =
  match OpamFile.OPAM.extended opam "x-maintained" Fun.id with
  | None -> true
  | Some { pelem = Bool b ; _ } -> b
  | _ -> invalid_arg "maintained: expected a bool"

let eval_pkgs pkg_dir pkgs pkg_all =
  match pkgs, pkg_all with
  | [], true ->
    let dh = Unix.opendir (Fpath.to_string pkg_dir) in
    let rec loop acc =
      match Unix.readdir dh with
      | exception End_of_file -> acc
      | pkg -> loop (pkg :: acc)
    in
    let acc = loop [] in
    Unix.closedir dh;
    acc
  | _, true -> invalid_arg "both --pkg and --pkg-all not supported"
  | _, false -> pkgs

let should_consider ?excluded path =
  if Fpath.filename path = "opam" then
    let name, version = pkg_name_and_version path in
    let is_excluded = match excluded with
      | None -> false
      | Some x -> List.mem version x
    in
    if is_excluded then
      None
    else
      let opam =
        let opam_file =
          OpamFile.make (OpamFilename.raw (Fpath.to_string path))
        in
        OpamFile.OPAM.read opam_file
      in
      Some (name, version, opam)
  else
    None

let find_opams_latest_first pkg_dir pkg =
  let ( let* ) = Result.bind in
  let foreach path acc =
    let* opams = acc in
    match should_consider path with
    | None -> Ok opams
    | Some (_, v, opam) -> Ok ((v, opam) :: opams)
  in
  let* opams =
    Bos.OS.Dir.fold_contents foreach (Ok []) Fpath.(pkg_dir / pkg)
  in
  let* opams = opams in
  Ok (List.sort (fun (v, _) (v', _) ->
      OpamVersionCompare.compare (version v') (version v))
      opams)

let decode_intent pkg opam =
  let intent =
    let default = "(any)" in
    let open OpamParserTypes.FullPos in
    match OpamFile.OPAM.extended opam "x-maintenance-intent" Fun.id with
    | None -> default
    | Some { pelem = List { pelem = [ one ] ; _ } ; _ } ->
      let extract_string = function
        | { pelem = String s ; _ } -> s
        | x ->
          Logs.warn (fun m -> m "%s intent failure: expected a string, got %s" pkg
                        (OpamPrinter.FullPos.value x));
          default
      in
      extract_string one
    | Some x ->
      Logs.warn (fun m -> m "%s intent failure: expected a list of a single string, got %s"
                    pkg (OpamPrinter.FullPos.value x));
      default
  in
  try Mintent.M.intent_of_string intent with
  | Failure _ ->
    Logs.warn (fun m -> m "%s invalid intent: %s, using any" pkg intent);
    [ Mintent.M.Last max_int ]

let eval_intent contexts pkg sorted (intent : Mintent.M.intent) =
  match intent with
  | Mintent.M.Last x :: [] when x = max_int ->
    (* if any, we output all *)
    let opams = List.filter not_maintained sorted in
    let keeping = List.map fst opams in
    let remove =
      let s = S.of_list (List.map fst sorted) in
      S.elements (S.diff s (S.of_list keeping))
    in
    (* Logs.app (fun m -> m "%s intent is any" pkg); *)
    List.iter (fun pkg -> Logs.app (fun m -> m "CANDIDATE (any) %s" pkg)) remove;
    remove
  | Mintent.M.Last 1 :: [] ->
    (* TODO do we need to filter out pre-releases if they're the latest? *)
    (* latest! we go through all ocaml versions and find the latest package *)
    let keeping = solve_by_ocaml_version contexts pkg in
    (* TODO what about the x-maintenance: false ones? *)
    (* let opams = List.filter not_maintained (M.bindings opams) in *)
    let remove =
      S.elements (S.diff (S.of_list (List.map fst sorted)) keeping)
    in
    (*Logs.app (fun m -> m "%s intent is latest" pkg);*)
    List.iter (fun pkg -> Logs.app (fun m -> m "CANDIDATE (latest) %s" pkg))
      remove;
    remove
  | Mintent.M.Last 0 :: [] ->
    (*Logs.app (fun m -> m "%s intent is none, keeping nothing" pkg);*)
    let remove = List.map fst sorted in
    List.iter (fun pkg -> Logs.app (fun m -> m "CANDIDATE (none) %s" pkg))
      remove;
    remove
  | _ ->
    let opams = List.filter not_maintained sorted in
    let keeping = List.map fst opams in
    let remove =
      S.elements (S.diff (S.of_list (List.map fst sorted)) (S.of_list keeping))
    in
    let int = Mintent.M.string_of_intent intent in
    Logs.warn (fun m -> m "%s intent is %s (not handled)" pkg int);
    List.iter (fun pkg -> Logs.app (fun m -> m "CANDIDATE (%s) %s" int pkg))
      remove;
    remove

let string_of_relop = OpamPrinter.FullPos.relop_kind

let rec filter_to_string = function
  | OpamTypes.FBool b -> string_of_bool b
  | FString s -> "\"" ^ s ^ "\""
  | FIdent (_opt_names, var, _env) ->
    OpamVariable.to_string var
  | FOp (f, rel, g) ->
    filter_to_string f ^ " " ^ string_of_relop rel ^ " " ^ filter_to_string g
  | FAnd (f, g) ->
    filter_to_string f ^ " && " ^ filter_to_string g
  | FOr (f, g) ->
    filter_to_string f ^ " || " ^ filter_to_string g
  | FNot f -> "not " ^ filter_to_string f
  | FDefined f -> "defined " ^ filter_to_string f
  | FUndef f -> "undefined " ^ filter_to_string f

let f_to_string = function
  | OpamTypes.Filter filter -> filter_to_string filter
  | Constraint (relop, filter) ->
    string_of_relop relop ^ " " ^ filter_to_string filter

let rec condition_to_string = function
  | OpamTypes.Empty -> ""
  | Atom f -> f_to_string f
  | Block a -> condition_to_string a
  | And (a, b) -> condition_to_string a ^ " & " ^ condition_to_string b
  | Or (a, b) -> condition_to_string a ^ " | " ^ condition_to_string b

let is_installable opams opam =
  Logs.info (fun m -> m "installable of opam %s version %s"
               (OpamPackage.Name.to_string (OpamFile.OPAM.name opam))
               (OpamPackage.Version.to_string (OpamFile.OPAM.version opam)));
  let find_available name =
    OpamPackage.Set.fold (fun pkg acc ->
        if OpamPackage.Name.equal pkg.OpamPackage.name name then
          (OpamPackage.Version.to_string pkg.OpamPackage.version) :: acc
        else
          acc) opams []
  in
  let current_deps = OpamFile.OPAM.depends opam in
  let rec deps_good e = function
    | OpamFormula.Empty -> true, e
    | Atom (name, condition) ->
      Logs.info (fun m -> m "deps good %s" (OpamPackage.Name.to_string name));
      (* we've to find name in opams, and figure whether condition is satisfied *)
      let all_available = find_available name in
      (* esp. in conjunctions ("foo" {>= "1.0" & < "1.3"}) we need to track the
         matching candidates across the "&" - otherwise we may select "2.0" for
         the first conjunct, and 0.3 for the second. That's why we use a
         reference cell here. *)
      let available = ref all_available in
      let relop_cmp x = function
        | `Eq -> x = 0
        | `Geq -> x >= 0
        | `Gt -> x > 0
        | `Leq -> x <= 0
        | `Lt -> x < 0
        | `Neq -> x <> 0
      in
      let combine_f op a b = match a, b with
        | `Bool a, `Bool b -> `Bool (op a b)
        | `Always, _ | _, `Always -> `Always
      in
      let rec matches_filter = function
        | OpamTypes.FBool b -> `Bool b
        | FString s ->
          Logs.info (fun m -> m "matches_filter: string %s" s);
          `Bool true
        | FIdent (_opt_names, var, _env) ->
          begin match OpamVariable.to_string var with
            | "dev" | "with-doc" | "with-test" | "with-dev-setup" -> `Always
            | "build" | "post" -> `Bool true
            | _ ->
              Logs.info (fun m -> m "matches_filter: ident %s" (OpamVariable.to_string var));
              `Bool true
          end
        | FOp (f, rel, g) ->
          begin match f with
            | FIdent (_, var, _) when OpamVariable.to_string var = "os" ->
              `Bool true
            | _ ->
              Logs.info (fun m -> m "matches_filter: %s %s %s" (filter_to_string f)
                            (string_of_relop rel) (filter_to_string g));
              `Bool true
          end
        | FAnd (f, g) ->
          combine_f ( && ) (matches_filter f) (matches_filter g)
        | FOr (f, g) ->
          combine_f ( || ) (matches_filter f) (matches_filter g)
        | FNot f ->
          begin match matches_filter f with
            | `Bool b -> `Bool (not b)
            | `Always ->
              Logs.info (fun m -> m "matches_filter: not %s resulted in true" (filter_to_string f));
              `Bool true
          end
        | FDefined f ->
          Logs.info (fun m -> m "matches_filter: defined %s" (filter_to_string f));
          `Bool true
        | FUndef f ->
          Logs.info (fun m -> m "matches_filter: undefined %s" (filter_to_string f));
          `Bool true
      in
      let rec matches_condition = function
        | OpamTypes.Empty ->
          Logs.debug (fun m -> m "matches_condition: empty");
          `Bool true
        | Atom (OpamTypes.Filter f) ->
          Logs.debug (fun m -> m "matches_condition: filter %s" (filter_to_string f));
          matches_filter f
        | Atom (Constraint (relop, f)) ->
          Logs.debug (fun m -> m "matches_condition: constraint %s %s"
                        (string_of_relop relop)
                        (filter_to_string f));
          let r =
            let v =
              match f with
              | OpamTypes.FString s -> Some s
              | FIdent (_opt_names, var, _env) when OpamVariable.to_string var = "version" ->
                Some (OpamPackage.Version.to_string (OpamFile.OPAM.version opam))
              | _ -> None
            in
            match v with
            | None ->
              Logs.info (fun m -> m "matches_condition: unexpected filter %s"
                            (filter_to_string f));
              true
            | Some v ->
              available :=
                List.filter (fun ver ->
                    let r = relop_cmp (OpamVersionCompare.compare ver v) relop in
                    Logs.debug (fun m -> m "%s %s %s = %B" ver (string_of_relop relop) v r);
                    r)
                  !available;
              !available <> []
          in
          Logs.debug (fun m -> m "matches_condition result %B" r);
          `Bool r
        | Block a ->
          Logs.debug (fun m -> m "matches_condition: block");
          matches_condition a
        | And (a, b) ->
          Logs.debug (fun m -> m "matches_condition: and");
          let a = matches_condition a in
          let b = matches_condition b in
          Logs.debug (fun m -> m "matches_condition: and - combining %s with %s"
                         (match a with `Bool true -> "bool true" | `Bool false -> "bool false" | `Always -> "always")
                         (match b with `Bool true -> "bool true" | `Bool false -> "bool false" | `Always -> "always"));
          let r = combine_f ( && ) a b in
          Logs.debug (fun m -> m "matches_condition: and result %s"
                         (match r with `Bool true -> "bool true" | `Bool false -> "bool false" | `Always -> "always"));
          r
        | Or (a, b) ->
          Logs.debug (fun m -> m "matches_condition: or");
          let a = matches_condition a in
          available := all_available;
          let b = matches_condition b in
          available := all_available;
          combine_f ( || ) a b
      in
      let r =
        match matches_condition condition with
        | `Bool b -> b && !available <> []
        | `Always -> true
      in
      let e =
        if not r then begin
          let cond = condition_to_string condition in
          let reason =
            "\"" ^ OpamPackage.Name.to_string name ^ "\"" ^
            (if cond = "" then "" else " { " ^ cond ^ " }")
          in
          reason :: e
        end else
          e
      in
      r, e
    | Block x -> deps_good e x
    | And (a, b) ->
      let a', ea = deps_good e a in
      let b', eb = deps_good ea b in
      a' && b', eb
    | Or (a, b) ->
      let a', ea = deps_good e a in
      let b', eb = deps_good ea b in
      a' || b', eb
  in
  deps_good [] current_deps

let ignore_packages = S.of_list [
    "conf-freeglut.1" ; (* { build & os-distribution != "debian" & os-distribution != "ubuntu" & not os-distribution = "ol" | not os-version < "9" } *)
    "ocaml-option-spacetime.1" ; (* "ocaml-variants" { post & >= "4.12.0~" & < "4.12" } *)
    "ocamlmig.5.2-20250129" ; (* "ocamlformat-rpc-lib" { "1" = "0" & = version } *)
    "ocamlmig.5.2-20250228" ; (* "ocamlformat-rpc-lib" { "1" = "0" & = version } *)
    "ocamlmig.5.2-20250228" ; (* "ocamlformat-rpc-lib" { "1" = "0" & = version } *)
    "ocamlmig.5.3-20250429" ; (* "ocamlformat-rpc-lib" { "1" = "0" & = version } *)
    "ocamlmig.5.4-20251020" ; (* "ocamlformat-rpc-lib" { "1" = "0" & = version } *)
]

let to_ignore = S.of_list [
    "chrome-trace" ; "dune" ; "dune-action-plugin" ; "dune-build-info" ;
    "dune-configurator" ; "dune-glob" ; "dune-private-libs" ; "dune-rpc" ;
    "dune-rpc-lwt" ; "dune-site" ; "dyn" ; "ocamlc-loc" ; "ordering" ;
    "stdune" ; "xdg" ; "fs-io" ; "top-closure" ; (* for the rocq folks *)
]

let jump () opam_repository pkgs pkg_all remove_file =
  OpamCoreConfig.update ();
  let ( let* ) = Result.bind in
  let pkg_dir = Fpath.(v opam_repository / "packages") in
  let* _ = Bos.OS.Dir.must_exist pkg_dir in
  let contexts = List.map (context opam_repository) ocaml_versions in
  let pkgs = eval_pkgs pkg_dir pkgs pkg_all in
  (* Phase 1: a set of candidates to archive based on maintenance intent *)
  Logs.app (fun m -> m "PHASE1 finding packages to archive (based on maintenance intent)");
  let* to_remove =
    match remove_file with
    | Some filename ->
      (* Phase 1a: we already computed this step, and take input from a file *)
      let* lines = Bos.OS.File.read_lines (Fpath.v filename) in
      let pkgs =
        List.fold_left (fun acc line ->
            if String.starts_with ~prefix:"CANDIDATE" line then
              let second_space = succ (String.index_from line 10 ' ') in
              let pkg =
                String.sub line second_space (String.length line - second_space)
              in
              pkg :: acc
            else
              acc
          ) [] lines
      in
      Ok pkgs
    | None ->
      (* Phase 1 for real: figure opam file, x-maintenance-intent, solve what to retain *)
      List.fold_left (fun acc pkg ->
          let* acc = acc in
          let* sorted = find_opams_latest_first pkg_dir pkg in
          let intent = decode_intent pkg (snd (List.hd sorted)) in
          let to_remove = eval_intent contexts pkg sorted intent in
          Ok (to_remove @ acc))
        (Ok []) pkgs
  in
  Logs.app (fun m -> m "PHASE1 completed with %u packages" (List.length to_remove));
  (* Phase 2: evaluate which packages would have unsatisfied dependencies *)
  Logs.app (fun m -> m "PHASE2 finding packages that are no longer installable");
  let all_opams =
    (OpamPackage.keys
       (OpamRepositoryState.load_opams_from_dir
          (OpamRepositoryName.of_string "temporary")
          (OpamFilename.Dir.of_string opam_repository)))
  in
  let all_opams =
    List.fold_left (fun opams rm ->
        OpamPackage.Set.remove (OpamPackage.of_string rm) opams)
      all_opams to_remove
  in
  let foreach path acc =
    match should_consider ~excluded:to_remove path with
    | None -> acc
    | Some (name, pkg_version, opam) ->
      let r, exp = is_installable all_opams opam in
      if r then
        acc
      else if S.mem pkg_version ignore_packages then
        acc
      else if S.mem name to_ignore then
        acc
      else
        (Logs.app (fun m -> m "%s would not be installable, due to: %a"
                      pkg_version Fmt.(list ~sep:(any ", ") string) exp);
         pkg_version :: acc)
  in
  let* r =
    Bos.OS.Dir.fold_contents foreach [] pkg_dir
  in
  Logs.app (fun m -> m "PHASE2 completed with %u packages" (List.length r));
  (* Phase 3: figure out what to not delete
     (run the solver again to figure which exact versions to restore) *)
  Logs.app (fun m -> m "PHASE3 figuring out which packages to retain from PHASE1 to avoid uninstallable packages");
  let to_remove_set = S.of_list to_remove in
  let retain =
    List.fold_left (fun acc pkg ->
        let package, version = package pkg, version pkg in
        let constraints =
          [ OpamPackage.Name.of_string package,
            (`Eq, OpamPackage.Version.of_string version) ]
        in
        let contexts =
          List.map (context ~constraints opam_repository) ocaml_versions
        in
        let retain = solve_by_ocaml_version ~retain_all:true contexts package in
        let to_retain = S.inter to_remove_set retain in
        Logs.app (fun m -> m "%s retaining %a" pkg
                      Fmt.(list ~sep:(any ", ") string) (S.elements to_retain));
        S.union acc to_retain
      ) S.empty r
  in
  let remove = S.diff to_remove_set retain in
  Logs.app (fun m -> m "PHASE3 completed, will archive %u packages (%u candidates): %a"
               (S.cardinal remove)
               (S.cardinal to_remove_set)
               Fmt.(list ~sep:(any ", ") string)
               (S.elements remove));
  List.iter (fun pkg -> Logs.app (fun m -> m "PHASE3 ARCHIVING %s" pkg)) (S.elements remove);
  Ok ()

let setup_log style_renderer level =
  Fmt_tty.setup_std_outputs ?style_renderer ();
  Logs.set_level level;
  Logs.set_reporter (Logs_fmt.reporter ~dst:Format.std_formatter ())

open Cmdliner

let setup_log =
  Term.(const setup_log
        $ Fmt_cli.style_renderer ()
        $ Logs_cli.level ())

let pkg =
  let doc = "Archive this package (may be package name or package.version)" in
  Arg.(value & opt_all string [] & info ~doc ["pkg"])

let pkg_all =
  let doc = "Consider all packages" in
  Arg.(value & flag & info ~doc ["pkg-all"])

let opam_repository =
  let doc = "Opam repository directory to work on (must be a git checkout)" in
  Arg.(value & opt dir "." & info ~doc ["opam-repository"])

let remove_file =
  let doc = "Skip the maintenance intent check, and provide a file with things to remove" in
  Arg.(value & opt (some file) None & info ~doc ["remove-file"])

let cmd =
  let info = Cmd.info "maintenance-intent" ~version:"%%VERSION_NUM%%"
  and term =
    Term.(term_result (const jump $ setup_log $ opam_repository $ pkg $ pkg_all $ remove_file))
  in
  Cmd.v info term

let () = exit (Cmd.eval cmd)
