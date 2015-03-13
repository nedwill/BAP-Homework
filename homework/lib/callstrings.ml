open Core_kernel.Std
open Bap.Std
open Program_visitor

let calls syms insns =
  Seq.concat_map insns ~f:(
    fun (_mem, insn) ->
      let visitor = (object inherit [string seq] Bil.visitor
        method! enter_int addr calls =
          if in_jmp then
            match Table.find_addr syms addr with
            | None -> calls
            | Some (mem, dst) ->
              if Addr.(Memory.min_addr mem = addr) then
                Seq.cons dst calls
              else calls
          else calls
      end) in visitor#run (Insn.bil insn) Seq.empty)

let all_calls p =
  let string_tab = Table.mapi p.symbols ~f:(
    fun mem src ->
      Seq.map (calls p.symbols (Disasm.insns_at_mem p.program mem)) ~f:(
        fun dst -> (src, dst))) in
  let flattened = Seq.concat_map ~f:snd (Table.to_sequence string_tab) in
  Seq.mapi flattened ~f:(fun i (src, dst) -> (i, src, dst))

let callstrings _p _root = Seq.empty

(*
(* use these to store callstring as an int *)
let callstring_of_list = ()
let list_of_callstring = ()

exception Empty

let rec end_of_list = function
  | [] -> raise Empty
  | [x] -> x
  | _::l -> end_of_list l

(* c is a call site info seq for now, should be a map, from all_calls *)
let kstrings_of_callmap k c =
  let grow_list cs_list element = (* this could be refactored *)
    let len = length cs_list in
    if len > k then
      raise SizeError
    else if len = k then
      match cs_list with
      | [] -> raise SizeError
      | x::l -> l @@ [element]
    else
      cs_list @@ [element]
  in
  let g cs_list next_possible =
    Set.fold next_possible (grow_list cs_list)
  in
  let f cs = 
    let cs_list = list_of_callstring cs in
    let (_, _, last_dst) = end_of_list cs_list in (* exn if empty? *)
    let next_possible =
      Map.filter ~f:(fun (_, src, _) -> src = last_dest) cs
    in
    let cs' = Map.fold next_possible Set.empty g
  in
  let rec kstrings_of_callmap' s =
    let sz = length s in
    let new_callstrings_sets = Seq.map f s in
    let new_callstrings = Fold Set.empty Set.union new_callstrings_sets in
    if length new_callstrings = sz then
      new_callstrings
    else
      kstrings_of_callmap' new_callstrings
  in
  kstrings_of_callmap' Set.empty

(* Given a program and an integer k, return a table m where m maps from
 * a function to a k-sensitive call string.
 *)
let kstrings p k = all_calls p |> (kstrings_of_callmap k)
*)

type call_site = int

type call_string =
  | Singleton of call_site
  | Cycle of call_site list

exception EmptyCycle

let flatten_list = List.fold ~init:[] ~f:(fun a b -> a @ b)

exception NoI
exception NotOneI

(* out-neighbors of v in g *)
let neighborhood (g : (call_site * bytes * bytes) list) (v : call_site) : call_site list = (* could filter_map *)
  let target_dst =
    begin match List.filter ~f:(fun (i, _src, _dst) -> i = v) g with
    | [] -> raise NoI
    | [(_i, _src, dst)] -> dst (* map as seq :/ *)
    | _::_ -> raise NotOneI
    end
  in
  List.filter ~f:(fun (_i, src, _dst) -> src = target_dst) g
  |> List.map ~f:(fun (i, _src, _dst) -> i)

(* gives all walks up to length k in digraph G starting from vertex v *)
let rec paths (g : (call_site * bytes * bytes) list) k v : call_site list list =
  let nbrhood = neighborhood g v in
  List.map ~f:(fun nbr -> (paths g (k-1) nbr)) nbrhood
  |> flatten_list
  |> List.map ~f:(fun path -> v::path)

(* return a list with duplicates removed *)
(* polymorphic compare should just work here *)
let rec dedupe_list = function
  | [] -> []
  | x::l -> x::(dedupe_list (List.filter ~f:(fun x' -> x <> x') l))

let get_first_element = function
  | Singleton site -> site
  | Cycle (x::_) -> x
  | Cycle ([]) -> raise EmptyCycle

let first_dupe_callstring l =
  let combine (first_dupe, current_set) element =
    let first_element = get_first_element element in
    begin match first_dupe with
    | None ->
      if Set.mem current_set first_element then
        (Some first_element, current_set)
      else
        (None, Set.add current_set first_element)
    | Some x -> (Some x, current_set)
    end
  in
  List.fold l ~init:(None, Set.empty ~comparator:Int.comparator) ~f:combine |> fst

exception NoDupeFound

(* Takes a walk of callstring elements and a vertex
   which is assumed to be the first duplicate element
   and returns the cycle that begins with that duplicate
   element.
   e.g. cycle_list ([a;b;c;a;b;c], a) -> [a;b;c]
   Note: We should have a unit test for this.
 *)
let cycle_list callstring_list v_dupe : call_site list =
  let rec clear_start = function
    | x::l when get_first_element x = v_dupe -> l
    | _::l -> clear_start l
    | [] -> raise NoDupeFound
  in
  let start_list =
    begin match callstring_list with
    | [] -> []
    | _::l -> l
    end
  in
  let dupe_start = clear_start start_list in
  let rec collect_cycle = function
    | x::_ when get_first_element x = v_dupe -> []
    | x::l -> (get_first_element x)::(collect_cycle l)
    | [] -> raise NoDupeFound (* didn't find the other element *)
  in
  collect_cycle dupe_start |> List.rev

let rec prefix_matches l (cycle_l : call_site list) =
  match (l, cycle_l) with
  | ((Singleton x)::l, x'::l') ->
    if x = x' then prefix_matches l l' else false
  | ((Cycle _::_), _::_) -> false
  | ([], _::_) -> false
  | (_::_, []) -> false
  | ([], []) -> true

exception NotMatching

let rec drop_cycle_prefix l (cycle_l : call_site list) : call_string list =
  match (l, cycle_l) with
  | ((Singleton x')::l', x''::l'') ->
    if x' <> x'' then
      raise NotMatching
    else
      drop_cycle_prefix l' l''
  | (_, []) -> l
  | _ -> raise NotMatching

(* replace runs of singletons in l with Cycle (cycle_l) *)
let replace_cycles (l : call_string list) (cycle_l : call_site list) : call_string list =
  let rec replace_cycles' (l : call_string list) : call_string list =
    match l with
    | [] -> []
    | x::l' ->
      if prefix_matches (x::l') cycle_l then
        let dropped : call_string list = drop_cycle_prefix l' cycle_l
        |> replace_cycles' in (* careful, not tail recursive *)
        (Cycle cycle_l)::dropped
      else
        x::(replace_cycles' l')
  in
  replace_cycles' l

(* takes a walk of callsites (ints) from a graph and makes a callstring list *)
let callstring_of_callsite_list (l : call_site list) : call_string list =
  let rec callstring_of_callsite_list' l' =
    begin match first_dupe_callstring l' with
    | None -> l' (* no duplicates => no cycles remaining *)
    | Some v_dupe ->
      let cycle_l = cycle_list l' v_dupe in
      (* replace cycles with one Cycle node *)
      replace_cycles l' cycle_l |> dedupe_list
      |> callstring_of_callsite_list'
    end
  in
  List.map l ~f:(fun x -> Singleton x)
  |> callstring_of_callsite_list'
  |> dedupe_list

exception Empty

let rec split_on_last : call_string list -> (call_site * call_string list) = function
  | [] -> raise Empty
  | x::[] ->
    begin match x with
    | Singleton x' -> (x', [])
    | Cycle (x'::_) -> (x', [])
    | Cycle ([]) -> raise EmptyCycle
    end
  | x::l -> let (x', l') = split_on_last l in (x', x::l')

let make_map (callstring_list : call_string list list) =
  List.map ~f:split_on_last callstring_list
  |> Int.Map.of_alist_exn

let get_subpaths_one_path (l : call_string list) =
  let rec subpaths l a =
    begin match l with
    | [] -> a (* don't include empty path *)
    | _::l' -> subpaths l' (l::a)
    end
  in
  subpaths l [] |> flatten_list

let get_subpaths_list (l : call_string list list) =
  List.map ~f:get_subpaths_one_path l |> dedupe_list

(* Given a program, return a table m where m maps from a function to
 * the acyclic call string.
 *)
let astrings p =
  let g = p |> all_calls |> Seq.to_list in
  let num_vertices = 2*(List.length g) in
  List.map ~f:(fun (i, _src, _dst) ->
    paths g num_vertices i
    |> List.map ~f:callstring_of_callsite_list
    |> get_subpaths_list
  ) g |> flatten_list |> dedupe_list |> make_map
