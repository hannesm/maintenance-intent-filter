
let ocaml_versions = [
  "4.08.0"; "4.09.0"; "4.10.0"; "4.11.0"; "4.12.0"; "4.13.0"; "4.14.0";
  "5.0.0"; "5.1.0"; "5.2.0"; "5.3.0"
]

module S = Set.Make(String)
module M = Map.Make(String)

let version s =
  let dot = String.index s '.' in
  String.sub s dot (String.length s - dot)

let env =
  Opam_0install.Dir_context.std_env
    ~arch:"x86_64"
    ~os:"linux"
    ~os_family:"debian"
    ~os_distribution:"debian"
    ~os_version:"10"
    ()

let context dir compiler_version =
  let constraints =
    OpamPackage.Name.Map.of_list [
      OpamPackage.Name.of_string "ocaml",
      (`Eq, OpamPackage.Version.of_string compiler_version)
    ]
  in
  Opam_0install.Dir_context.create (dir ^ "/packages") ~constraints ~env

module Solver = Opam_0install.Solver.Make(Opam_0install.Dir_context)

let solve context package =
  let pkg = OpamPackage.Name.of_string package in
  let result = Solver.solve context [ pkg ] in
  match result with
  | Error e -> Error (Solver.diagnostics e)
  | Ok selections ->
    Ok (List.find (fun p -> OpamPackage.Name.equal (OpamPackage.name p) pkg)
          (Solver.packages_of_result selections))

let solve_by_ocaml_version contexts package_name =
  let to_keep =
    List.fold_left2 (fun acc context ocaml_version ->
        match solve context package_name with
        | Ok pkg -> S.add (OpamPackage.to_string pkg) acc
        | Error _ -> Logs.warn (fun m -> m "%s for ocaml %s got no solution" package_name ocaml_version); acc)
      S.empty contexts ocaml_versions
  in
  (*Logs.app (fun m -> m "0install keeping %a" Fmt.(list ~sep:(any ", ") string)
               (S.elements to_keep));*)
  to_keep

let find_ocaml_dep v opam =
  let ocaml_dep = OpamPackage.Name.of_string "ocaml" in
  let deps = OpamFile.OPAM.depends opam in
  let dep_matches op filter =
    match filter with
    | OpamTypes.FString ver ->
      begin
        let r = match op with
          | `Lt -> OpamVersionCompare.compare v ver <= 0
          | `Leq | `Eq -> OpamVersionCompare.compare v ver < 0
          | `Geq -> OpamVersionCompare.compare v ver >= 0
          | `Gt -> OpamVersionCompare.compare v ver >= 0
          | `Neq -> false
        in
        (*Logs.app (fun m -> m "ocaml version %s op %s ver %s == %B" v
                     (OpamPrinter.FullPos.relop_kind op)
                     ver r); *)
        r
      end
    | _ -> false
  in
  let rec walk_formula p = function
    | OpamTypes.Empty -> false
    | Atom f -> p f
    | Block formula -> walk_formula p formula
    | And (a, b) -> walk_formula p a && walk_formula p b
    | Or (a, b) -> walk_formula p a || walk_formula p b
  in
  let p = function
    | OpamTypes.Filter _ -> false
    | Constraint (op, filter) -> dep_matches op filter
  in
  let rec find_dep = function
    | OpamFormula.Empty -> false
    | Atom (name, cond) ->
      if OpamPackage.Name.equal ocaml_dep name then
        walk_formula p cond
      else
        false
    | Block x -> find_dep x
    | And (a, b) ->
      let a' = find_dep a in
      let b' = find_dep b in
      a' || b'
    | Or (a, b) ->
      let a' = find_dep a in
      let b' = find_dep b in
      a' && b'
  in
  find_dep deps

let find_latest opams =
  List.fold_left (fun acc ocaml_version ->
      (* Logs.app (fun m -> m "for ocaml version %s" ocaml_version); *)
      match List.find_opt (fun (_, opam) -> find_ocaml_dep ocaml_version opam) opams with
      | None -> acc
      | Some (version, opam) ->
        (* Logs.app (fun m -> m "keeping %s" version); *)
        M.add version opam acc
    ) M.empty ocaml_versions

let pkg_name_and_version path =
  match List.rev (Fpath.segs path) with
  | _opam :: pkg_ver :: pkg :: _rest -> pkg, pkg_ver
  | _ -> assert false

let not_maintained (_, opam) =
  match OpamFile.OPAM.extended opam "x-maintained" Fun.id with
  | None -> true
  | Some { pelem = Bool b ; _ } -> b
  | _ -> invalid_arg "maintained: expected a bool"

let jump () opam_repository pkgs pkg_all =
  let ( let* ) = Result.bind in
  let pkg_dir = Fpath.(v opam_repository / "packages") in
  let* _ = Bos.OS.Dir.must_exist pkg_dir in
  let contexts = List.map (context opam_repository) ocaml_versions in
  let pkgs = match pkgs, pkg_all with
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
  in
  let should_consider path =
    if Fpath.filename path = "opam" then
      let _name, version = pkg_name_and_version path in
      let opam =
        let opam_file =
          OpamFile.make (OpamFilename.raw (Fpath.to_string path))
        in
        OpamFile.OPAM.read opam_file
      in
      Some (version, opam)
    else
      None
  in
  let foreach path acc =
    let* opams = acc in
    match should_consider path with
    | None -> Ok opams
    | Some p -> Ok (p :: opams)
  in
  List.fold_left (fun acc pkg ->
      (* for each pkg, we collect all opam files *)
      let* () = acc in
      let* opams =
        Bos.OS.Dir.fold_contents foreach (Ok []) Fpath.(pkg_dir / pkg)
      in
      let* opams = opams in
      let sorted =
        List.sort
          (fun (v, _) (v', _) -> OpamVersionCompare.compare (version v') (version v))
          opams
      in
      (* we parse the x-maintenance-intent of the last version *)
      let* intent =
        let default = "(any)" in
        let open OpamParserTypes.FullPos in
        match OpamFile.OPAM.extended (snd (List.hd sorted)) "x-maintenance-intent" Fun.id with
        | None -> Ok default
        | Some { pelem = List { pelem = [ one ] ; _ } ; _ } ->
          let extract_string = function
            | { pelem = String s ; _ } -> Ok s
            | x ->
              Logs.warn (fun m -> m "%s intent failure: expected a string, got %s" pkg
                            (OpamPrinter.FullPos.value x));
              Ok default
          in
          extract_string one
        | Some x ->
          Logs.warn (fun m -> m "%s intent failure: expected a list of a single string, got %s"
                        pkg (OpamPrinter.FullPos.value x));
          Ok default
      in
      let intent =
        try Mintent.M.intent_of_string intent with
        | Failure _ ->
          Logs.warn (fun m -> m "%s invalid intent: %s, using any" pkg intent);
          [ Mintent.M.Last max_int ]
      in
      (* if none, we output none *)
      (match intent with
       | Mintent.M.Last x :: [] when x = max_int ->
         (* if any, we output all *)
         let opams = List.filter not_maintained sorted in
         let keeping = List.map fst opams in
         let remove = S.elements (S.diff (S.of_list (List.map fst sorted)) (S.of_list keeping)) in
         (*Logs.app (fun m -> m "%s intent is any" pkg);*)
         List.iter (fun pkg -> Logs.app (fun m -> m "REMOVING (any) %s" pkg)) remove
       | Mintent.M.Last 1 :: [] ->
         (* latest! we go through all ocaml versions and find the latest package *)
         let keeping = solve_by_ocaml_version contexts pkg in
         (* let opams = find_latest sorted in
         let opams = List.filter not_maintained (M.bindings opams) in
            let keeping = List.map fst opams in *)
         let remove = S.elements (S.diff (S.of_list (List.map fst sorted)) keeping) in
         (*Logs.app (fun m -> m "%s intent is latest" pkg);*)
         List.iter (fun pkg -> Logs.app (fun m -> m "REMOVING (latest) %s" pkg)) remove
       | Mintent.M.Last 0 :: [] ->
         (*Logs.app (fun m -> m "%s intent is none, keeping nothing" pkg);*)
         List.iter (fun pkg -> Logs.app (fun m -> m "REMOVING (none) %s" pkg)) (List.map fst sorted)
       | _ ->
         let opams = List.filter not_maintained sorted in
         let keeping = List.map fst opams in
         let remove = S.elements (S.diff (S.of_list (List.map fst sorted)) (S.of_list keeping)) in
         Logs.warn (fun m -> m "%s intent is %s (not handled)" pkg
                       (Mintent.M.string_of_intent intent));
         List.iter (fun pkg -> Logs.app (fun m -> m "REMOVING (%s) %s" (Mintent.M.string_of_intent intent) pkg)) remove
      );
      Ok ())
    (Ok ()) pkgs

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

let cmd =
  let info = Cmd.info "maintenance-intent" ~version:"%%VERSION_NUM%%"
  and term =
    Term.(term_result (const jump $ setup_log $ opam_repository $ pkg $ pkg_all))
  in
  Cmd.v info term

let () = exit (Cmd.eval cmd)
