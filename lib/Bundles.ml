(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 and MIT Licenses. *)

(** Collapsing several F* modules into a single "bundle" to allow more static
 * uses. *)

open Bundle
open Ast

module StringMap = Map.Make(String)


let uniq =
  let r = ref (-1) in
  fun () ->
    incr r;
    !r

let mark_private =
  let add_if name flags =
    let is_private = List.mem Common.Private flags in
    if not is_private && not (Inlining.always_live name) then
      Common.Private :: flags
    else
      flags
  in
  function
  | DFunction (cc, flags, n_cgs, n, typ, name, binders, body) ->
      DFunction (cc, add_if name flags, n_cgs, n, typ, name, binders, body)
  | DGlobal (flags, name, n, typ, body) ->
      DGlobal (add_if name flags, name, n, typ, body)
  | DType (lid, flags, n_cgs, n, def) ->
      DType (lid, add_if lid flags, n_cgs, n, def)
  | DExternal (cc, flags, n_cg, n, lid, t, pp) ->
      DExternal (cc, add_if lid flags, n_cg, n, lid, t, pp)

(** This collects all the files that match a given bundle specification, while
 * preserving their original dependency ordering within the bundle. If the
 * bundle is of the form Apis=Patterns, then the declarations from any of Apis
 * are kept as-is, while declarations from the modules that match the Patterns
 * are marked as private. Assuming no cross-translation-unit calls happen, this
 * means a C static qualifier in the extracted code.
 *
 * The used parameter is just here to keep track of which files have been
 * involved in at least one bundle, so that we can drop them afterwards. *)
let make_one_bundle (bundle: Bundle.t) (files: file list) (used: (int * Bundle.t) StringMap.t) =
  let debug = Options.debug "bundle" in
  if debug then
    KPrint.bprintf "Starting creation of bundle %s\n" (string_of_bundle bundle);

  let api, patterns, _ = bundle in
  (* The used map also allows us to detect when a file is used twice in a
   * bundle. *)
  let this_round = uniq () in

  let in_api_list name =
    List.mem name (List.map (String.concat "_") api)
  in

  (* Match a file against the given list of patterns. *)
  let match_file is_api patterns (used, found) (file: file) =
    List.fold_left (fun (used, found) pattern ->
      let name = fst file in
      (* [is_api] overrides the default behavior (don't collect) *)
      if Bundle.pattern_matches_file pattern name && (is_api || not (in_api_list name)) then begin
        if debug then
          KPrint.bprintf "%s is a match\n" name;

        (* If the file was already matched previously, don't match it a second time. *)
        let prev_round = try StringMap.find name used with Not_found -> max_int, ([], [], []) in
        if fst prev_round <= this_round then begin
          if is_api then
            (* Change into a non-fatal warning? Say nothing? *)
            Warn.fatal_error "The API file %s, in bundle %s, was matched \
              previously by bundle %s\n"
              name (string_of_bundle bundle) (string_of_bundle (snd prev_round));
          used, found
        end else
          let file = fst file, if is_api then snd file else List.map mark_private (snd file) in
          StringMap.add name (this_round, bundle) used, file :: found
      end else begin
        used, found
      end
    ) (used, found) patterns
  in

  (* Find all the files that match the given patterns. *)
  let used, found = List.fold_left (match_file false patterns) (used, []) files in

  (* The Api module gets a special treatment; if it exists, it is not collected
   * in the call to [fold_left] above; rather, it is taken now from the list of
   * files so that its declarations do not get the special "private" treatment. *)
  let used, found =
    if api = [] then
      used, found
    else
      let count = StringMap.cardinal used in
      if debug then
        KPrint.bprintf "Looking for bundle APIs\n";
      let used, found = List.fold_left (fun (used, found) api ->
        List.fold_left (match_file true [ Module api ]) (used, found) files
      ) (used, found) api in
      if StringMap.cardinal used <> count + List.length api then
        Warn.fatal_error "There an issue with your bundle.\n\
          You specified: -bundle %s\n\
          Here's the issue: one of these modules doesn't exist: %s.\n\
          Suggestion #1: if the file does exist, pass it to KaRaMeL.\n\
          Suggestion #2: if it doesn't, skip the %s= part and write -bundle %s"
          (string_of_bundle bundle)
          (string_of_apis api)
          (string_of_apis api)
          (string_of_patterns patterns);
      used, found
  in

  (* We return the updated map of all "used" original files *)
  let bundle = bundle_filename bundle, List.flatten (List.rev_map snd found) in
  used, bundle

type color = White | Gray | Black

type dependency = lident * string * lident * string

let string_of_dependency (d1, f1, d2, f2) =
  KPrint.bsprintf "%a (found in file %s) mentions %a (found in file %s)"
    PrintAst.plid d1 f1 PrintAst.plid d2 f2

let explain_loop files (edges: (lident * string * lident * string) list) =
  let edges = List.rev edges in
  let _, _, _, last_file = KList.last edges in
  let rec discard_prefix = function
    | ((_, file_from, _, _) :: _) as edges when file_from = last_file ->
        edges
    | _ :: edges ->
        discard_prefix edges
    | [] ->
        assert false
  in
  let edges = discard_prefix edges in
  let map = Helpers.build_map files (fun tbl decl ->
    Hashtbl.add tbl (lid_of_decl decl) decl
  ) in
  let b = Buffer.create 256 in
  let pclid buf (m, n) =
    Printf.bprintf buf "[ ";
    List.iter (fun m ->
      Printf.bprintf buf "%s; " m
    ) m;
    Printf.bprintf buf "%s ]" n
  in
  Printf.bprintf b "There is a dependency loop in %d steps\n\n" (List.length edges);
  List.iteri (fun i (decl_from, file_from, decl_to, file_to) ->
    Printf.bprintf b "STEP %d: file `%s` depends on file `%s`, because\n" i file_from file_to;
    let flavor = function
      | DType _ -> "type"
      | DFunction _ -> "function"
      | DGlobal _ -> "global"
      | DExternal _ -> "external"
    in
    let decl_from_def = Hashtbl.find map decl_from in
    let flavor_from = flavor decl_from_def in
    let decl_to_def = Hashtbl.find map decl_to in
    let flavor_to = flavor decl_to_def in
    let shrink = function
      | DFunction (cc, flags, n_cgs, n, typ, name, binders, _) ->
          DFunction (cc, flags, n_cgs, n, typ, name, binders, with_type TAny (EQualified ([], "// omitted")))
      | d -> d
    in
    let decl_from_def = shrink decl_from_def in
    let decl_to_def = shrink decl_to_def in
    let open PPrint in
    let open PrintAst in
    let open PrintCommon in
    let p = printf_of_pprint_pretty (fun d -> nest 4 (break1 ^^ group (print_decl d) ^^ hardline)) in
    Printf.bprintf b "The %s declaration below, known in config syntax as %a\n%a\n\
      depends on the %s declaration below, known in config syntax as %a\n%a\n\n"
      flavor_from pclid decl_from p decl_from_def
      flavor_to pclid decl_to p decl_to_def
  ) edges;
  Buffer.contents b

let direct_dependencies file_of file =
  let deps = Hashtbl.create 41 in
  let current_decl = ref None in
  let prepend lid =
    match file_of lid with
    | Some f when f <> fst file ->
        let dep = (Option.get !current_decl, fst file, lid, f) in
        Hashtbl.replace deps f dep
    | _ ->
        ()
  in
  (object
    inherit [_] iter as super
    method! visit_decl env decl =
      current_decl := Some (lid_of_decl decl);
      super#visit_decl env decl
    method! visit_EQualified _ lid =
      prepend lid
    method! visit_TQualified _ lid =
      prepend lid
    method! visit_TApp _ lid _ =
      prepend lid
  end)#visit_file () file;
  deps

let topological_sort files =
  (* We perform a dependency analysis on this set of files to figure out how to
   * order them; this is the creation of the dependency graph. Instead of merely
   * keeping a list of dependencies, we keep a hash-table that maps a dependency
   * to the [lident] that is responsible for the dependency, to have better
   * error messages. *)
  let graph = Hashtbl.create 41 in
  let file_of = mk_file_of files in
  List.iter (fun file ->
    let deps = direct_dependencies file_of file in
    Hashtbl.add graph (fst file) (ref White, deps, snd file)
  ) files;

  (* en.wikipedia.org/wiki/Topological_sorting *)
  let stack = ref [] in
  let rec dfs debug file =
    let r, deps, contents = Hashtbl.find graph file in
    match !r with
    | Black ->
        ()
    | Gray ->
        Warn.fatal_error "Bundling creates a dependency cycle:\n%s"
          (explain_loop files debug)
    | White ->
        r := Gray;
        Hashtbl.iter (fun f dep -> dfs (dep :: debug) f) deps;
        r := Black;
        stack := (file, contents) :: !stack
  in
  List.iter (dfs []) (List.rev_map fst files);
  List.rev !stack

(* Debug any intermediary AST as follows: *)
(* PPrint.(Print.(print (PrintAst.print_files files ^^ hardline))); *)

(* This creates bundles for every [-bundle] argument that was passed on the
 * command-line. *)
let make_bundles files =
  (* We create the set of files that are either freshly-generated bundles, or
   * files that were not involved in the creation of a bundle and that,
   * therefore, we probably should keep. *)
  let used, bundles = List.fold_left (fun (used, bundles) arg ->
    let used, bundle = make_one_bundle arg files used in
    used, bundle :: bundles
  ) (StringMap.empty, []) (List.rev !Options.bundle) in
  let files = List.filter (fun (n, _) -> not (StringMap.mem n used)) files @ bundles in

  let names, _ = List.split files in
  let uniq_names = List.sort_uniq compare names in
  if List.length uniq_names <> List.length names then begin
    let seen = Hashtbl.create 42 in
    List.iter (fun name ->
      if Hashtbl.mem seen name then
        Warn.(maybe_fatal_error ("", BundleCollision name));
      Hashtbl.add seen name ()
    ) names
  end;

  (* This is important, because bundling may creates cycles, that are broken
   * after removing (now-unused) functions. *)
  let files = Inlining.drop_unused files in

  topological_sort files

(* A more refined version of direct_dependencies (found above), which
   distinguishes between internal and public dependencies. Keeps less dependency
   information, too, since it does not need to generate precise error messages.
   To be used after Inlining has run.

   We do not run this on the C grammar (which would presumably be simpler,
   because by then we would have built both flavors of headers + C files),
   because it does not distinguish between lids and ids, and also because the
   grammar is convoluted and makes it hard to access the "name" of a
   declaration.
   
   So instead, we anticipate and rely on the fact that:
   - to compute the dependencies of the public header, one needs to visit public
     (not internal, not private) functions and type declarations, and
     - skip the body of functions unless they are "static header", and
     - skip the body of type declarations marked as C abstract structs
   - to compute the dependencies of the internal header, same deal
   - to compute the dependencies of the C header, same deal except all bodies
     are visited
*)

module StringSet = Set.Make(String)
module LidSet = Idents.LidSet

type deps = {
  internal: StringSet.t;
  public: StringSet.t;
}

type all_deps = {
  h: deps;
  internal_h: deps;
  c: deps;
}

let empty_deps = { internal = StringSet.empty; public = StringSet.empty }

let drop_dinstinction { internal; public } =
  List.of_seq (StringSet.to_seq (StringSet.union internal public))

class record_everything (gen_dep: ?constructor:unit -> lident -> _) = object(self)
  inherit [_] reduce as super
  method plus { internal = i1; public = p1 } { internal = i2; public = p2 } =
    { internal = StringSet.union i1 i2; public = StringSet.union p1 p2 }
  method zero = empty_deps
  method! visit_EQualified _ lid =
    gen_dep lid
  method! visit_TQualified _ lid =
    gen_dep lid
  method! visit_TApp () lid _ =
    gen_dep lid
  method! visit_EFlat ((_, t) as env) fields =
    match t with
    | TQualified lid ->
        self#plus
          (gen_dep ~constructor:() lid)
          (super#visit_EFlat env fields)
    | _ ->
        super#visit_EFlat env fields
end

let direct_dependencies_with_internal files file_of =
  (* Set of decls marked as internal *)
  let internal = List.fold_left (fun set (_, decls) ->
    List.fold_left (fun set decl ->
      if List.mem Common.Internal (Ast.flags_of_decl decl) then
        LidSet.add (Ast.lid_of_decl decl) set
      else
        set
    ) set decls
  ) LidSet.empty files in

  let c_abstract_struct = List.fold_left (fun set (_, decls) ->
    List.fold_left (fun set decl ->
      if List.mem Common.AbstractStruct (Ast.flags_of_decl decl) then
        LidSet.add (Ast.lid_of_decl decl) set
      else
        set
    ) set decls
  ) LidSet.empty files in

  List.fold_left (fun by_file file ->
    let gen_dep ?constructor (callee: lident) =
      match file_of callee with
      | Some f when f <> fst file && not (Helpers.is_primitive callee) ->
          let is_internal = LidSet.mem callee internal in
          if Options.debug "dependencies" then
            KPrint.bprintf "In file %s, reference to %a (in %sheader %s)\n"
              (fst file) PrintAst.plid callee (if is_internal then "internal " else "") f;
          if is_internal || constructor = Some () && LidSet.mem callee c_abstract_struct then
            { empty_deps with internal = StringSet.singleton f }
          else
            { empty_deps with public = StringSet.singleton f }
      | _ ->
          empty_deps
    in
    let is_inline_static lid = List.exists (fun p -> Bundle.pattern_matches_lid p lid) !Options.static_header in
    let header_deps which = object(self)
      inherit (record_everything gen_dep) as super

      method private concerns_us flags =
        match which with
        | `Public -> not (List.mem Common.Internal flags) && not (List.mem Common.Private flags)
        | `Internal ->  List.mem Common.Internal flags

      method! visit_DFunction env cc flags n_cgs n ret name binders body =
        (* KPrint.bprintf "function %a: concern us=%b %b %b \n" *)
        (*   PrintAst.Ops.plid name *)
        (*   (self#concerns_us flags) *)
        (*   (List.mem Common.Internal flags) (List.mem Common.Private flags); *)
        if self#concerns_us flags then
          if is_inline_static name then
            super#visit_DFunction env cc flags n_cgs n ret name binders body
          else
            (* ill-typed, but convenient *)
            super#visit_DFunction env cc flags n_cgs n ret name binders Helpers.eunit
        else
          super#zero

      method! visit_DType env name flags n_cgs n def =
        let is_c_abstract_struct = List.mem Common.AbstractStruct flags in
        if is_c_abstract_struct then
          (* In `header_deps`, a C abstract struct always concerns us because it appears both in the
             public (forward declaration, no body) and in the internal header (actual declaration). *)
          if which = `Public then
            super#visit_DType env name flags n_cgs n (Abbrev TUnit)
          else
            super#visit_DType env name flags n_cgs n def
        else if self#concerns_us flags then
          super#visit_DType env name flags n_cgs n def
        else
          super#zero

      method! visit_DGlobal env flags name n t body =
        if self#concerns_us flags then
          if is_inline_static name then
            super#visit_DGlobal env flags name n t body
          else
            super#visit_DGlobal env flags name n t Helpers.eunit
        else
          super#zero
    end in
    let deps = {
      h = (
        if Options.debug "dependencies" then
          KPrint.bprintf "PUBLIC %s\n" (fst file);
        (header_deps `Public)#visit_file () file);
      internal_h = (
        if Options.debug "dependencies" then
          KPrint.bprintf "INTERNAL %s\n" (fst file);
        (header_deps `Internal)#visit_file () file);
      c = (
        if Options.debug "dependencies" then
          KPrint.bprintf "C %s\n" (fst file);
        (new record_everything gen_dep)#visit_file () file);
    } in

    if not (StringSet.is_empty deps.h.internal) then
      Warn.fatal_error "Unexpected: %s depends on some internal headers: %s\n"
        (fst file)
        (String.concat ", " (List.of_seq (StringSet.to_seq deps.h.internal)));
       
    StringMap.add (fst file) deps by_file
  ) StringMap.empty files


let debug_deps deps =
  StringMap.iter (fun name { internal; public } ->
    KPrint.bprintf "%s --> internal: %s | public: %s\n" name
      (String.concat ", " (List.of_seq (StringSet.to_seq internal)))
      (String.concat ", " (List.of_seq (StringSet.to_seq public)))
  ) deps

(* Topologically sort declarations within each file so that type definitions
   appear after the types they depend on by value. This is needed because
   bundling + monomorphization can place type definitions in an order that
   violates C's requirement that types be defined before they are used by
   value in struct/union fields. *)
let sort_decls_within_files (files: Ast.files): Ast.files =
  let module LidMap = Map.Make(struct
    type t = lident
    let compare = compare
  end) in
  (* Collect by-value type dependencies for a type_def: types referenced directly
     (not behind a pointer) that need a full definition before this type. *)
  let by_value_deps type_def =
    let deps = ref [] in
    let is_under_pointer = ref false in
    (object
      inherit [_] iter
      method! visit_TBuf _ t _const =
        let saved = !is_under_pointer in
        is_under_pointer := true;
        (object inherit [_] iter method! visit_TQualified _ _ = () end)#visit_typ () t;
        is_under_pointer := saved
      method! visit_TQualified _ lid =
        if not !is_under_pointer then
          deps := lid :: !deps
    end)#visit_type_def () type_def;
    !deps
  in
  List.map (fun (name, decls) ->
    (* Build a map from lid to declaration index *)
    let lid_to_idx = List.fold_left (fun (acc, i) d ->
      (match d with
       | DType (lid, _, _, _, _) -> LidMap.add lid i acc
       | _ -> acc), i + 1
    ) (LidMap.empty, 0) decls |> fst in
    let arr = Array.of_list decls in
    let n = Array.length arr in
    (* Separate full DType decls from everything else (forwards, functions, etc.) *)
    let full_dtype_indices = ref [] in
    let other_indices = ref [] in
    Array.iteri (fun i d ->
      match d with
      | DType (_, _, _, _, (Flat _ | Variant _ | Union _ | Abbrev _ | Enum _)) ->
          full_dtype_indices := i :: !full_dtype_indices
      | _ -> other_indices := i :: !other_indices
    ) arr;
    let full_dtype_indices = List.rev !full_dtype_indices in
    let other_indices = List.rev !other_indices in
    (* Build adjacency among full DType declarations *)
    let deps_of = Array.make n [] in
    List.iter (fun i ->
      match arr.(i) with
      | DType (_, _, _, _, td) ->
          let dep_lids = by_value_deps td in
          List.iter (fun lid ->
            match LidMap.find_opt lid lid_to_idx with
            | Some j when j <> i -> deps_of.(i) <- j :: deps_of.(i)
            | _ -> ()
          ) dep_lids
      | _ -> ()
    ) full_dtype_indices;
    (* Topological sort of full DType declarations using Kahn's algorithm *)
    let in_degree = Array.make n 0 in
    let successors = Array.make n [] in
    List.iter (fun i ->
      List.iter (fun j ->
        successors.(j) <- i :: successors.(j);
        in_degree.(i) <- in_degree.(i) + 1
      ) deps_of.(i)
    ) full_dtype_indices;
    let queue = Queue.create () in
    List.iter (fun i ->
      if in_degree.(i) = 0 then Queue.push i queue
    ) full_dtype_indices;
    let sorted_dtypes = ref [] in
    while not (Queue.is_empty queue) do
      let i = Queue.pop queue in
      sorted_dtypes := i :: !sorted_dtypes;
      List.iter (fun j ->
        in_degree.(j) <- in_degree.(j) - 1;
        if in_degree.(j) = 0 then Queue.push j queue
      ) successors.(i)
    done;
    let sorted_dtypes = List.rev !sorted_dtypes in
    (* Append any DTypes not reached (cycles) in original order *)
    let in_sorted = Array.make n false in
    List.iter (fun i -> in_sorted.(i) <- true) sorted_dtypes;
    let remaining_dtypes = List.filter (fun i -> not in_sorted.(i)) full_dtype_indices in
    (* Collect lids that already have a Forward declaration *)
    let has_forward = Hashtbl.create 16 in
    List.iter (fun i ->
      match arr.(i) with
      | DType (lid, _, _, _, Forward _) -> Hashtbl.replace has_forward lid true
      | _ -> ()
    ) other_indices;
    (* Collect ALL type dependencies (including pointer) for each full DType *)
    let all_deps type_def =
      let deps = ref [] in
      (object
        inherit [_] iter
        method! visit_TQualified _ lid = deps := lid :: !deps
      end)#visit_type_def () type_def;
      !deps
    in
    (* Track which lids are defined so far; generate forward declarations only
       for types referenced (even by pointer) before their definition. *)
    let defined = Hashtbl.create 16 in
    List.iter (fun lid -> Hashtbl.replace defined lid true)
      (List.filter_map (fun i -> match arr.(i) with
        | DType (lid, _, _, _, Forward _) -> Some lid | _ -> None) other_indices);
    let extra_forwards = ref [] in
    let full_dtype_set = Hashtbl.create 16 in
    List.iter (fun i ->
      match arr.(i) with
      | DType (lid, _, _, _, (Flat _ | Variant _ | Union _)) ->
          Hashtbl.replace full_dtype_set lid true
      | _ -> ()
    ) (sorted_dtypes @ remaining_dtypes);
    List.iter (fun i ->
      (match arr.(i) with
       | DType (_, _, _, _, (Flat _ | Variant _ | Union _ as td)) ->
           let refs = all_deps td in
           List.iter (fun lid ->
             if not (Hashtbl.mem defined lid) && not (Hashtbl.mem has_forward lid)
                && Hashtbl.mem full_dtype_set lid then
               match LidMap.find_opt lid lid_to_idx with
               | Some j when j <> i ->
                   (match arr.(j) with
                    | DType (_, flags, n_cgs, n_params, (Flat _ | Variant _ | Union _)) ->
                        Hashtbl.replace has_forward lid true;
                        extra_forwards :=
                          DType (lid, flags, n_cgs, n_params, Forward FStruct) :: !extra_forwards
                    | _ -> ())
               | _ -> ()
           ) refs
       | _ -> ());
      (match arr.(i) with
       | DType (lid, _, _, _, _) -> Hashtbl.replace defined lid true
       | _ -> ())
    ) (sorted_dtypes @ remaining_dtypes);
    let extra_forwards = List.rev !extra_forwards in
    (* Split other_indices into: Forward DType declarations, then the rest *)
    let forward_others = List.filter (fun i ->
      match arr.(i) with DType (_, _, _, _, Forward _) -> true | _ -> false
    ) other_indices in
    let non_forward_others = List.filter (fun i ->
      match arr.(i) with DType (_, _, _, _, Forward _) -> false | _ -> true
    ) other_indices in
    let order = forward_others @ sorted_dtypes @ remaining_dtypes @ non_forward_others in
    name, extra_forwards @ List.map (fun i -> arr.(i)) order
  ) files
