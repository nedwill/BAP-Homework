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
                Seq.cons (addr, dst) calls
              else calls
          else calls
      end) in visitor#run (Insn.bil insn) Seq.empty)

let all_calls p =
  let string_tab = Table.mapi p.symbols ~f:(
    fun mem src ->
      Seq.map (calls p.symbols (Disasm.insns_at_mem p.program mem)) ~f:(
        fun (addr, dst) -> (addr, src, dst))) in
  let flattened = Seq.concat_map ~f:snd (Table.to_sequence string_tab) in
  (* we might want to fold into a table here from i to the tuple *)
  (* ok yeah this really needs to be a map. i'll change it soon *)
  Seq.mapi flattened ~f:(fun i (addr, src, dst) -> (i, addr, src, dst))

let callstrings p root = Seq.empty

(* use these to store callstring as an int *)
let callstring_of_list = ()
let list_of_callstring = ()

exception SizeError
exception Empty

let rec end_of_list = function
  | [] -> raise Empty
  | [x] -> x
  | x::l -> end_of_list l

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

type call_site = int

type call_string =
  | Singleton of call_site
  | Cycle of call_site list

(*
get all paths of up to length k starting from vertex v:
let N = nbh(v)
map x::(recursive dfs) over N

this will give us all paths up to length 2*|v|

now need
callstring_of_list:
map everything to singletons to start

loop:
maintain set of seen vertices, fold over the list
no duplicate: done
first duplicate:
  find list of elements in cycle
  go through list, replacing every cycle with the cycle node
  go through list, keeping only first cycle node
  recurse

in this case our table will be a seq.
dedupe list
then take all sublists for smaller sized graphs
the dedupe that and return as a seq
*)

exception EmptyCycle

(* gives all walks up to length k in digraph G starting from vertex v *)
let rec paths G k v =
  let nbrhood = neighborhood(v) in
  map ~f:(fun nbr -> v::(paths G (k-1) nbr)) nbrhood

(* return a list with duplicates removed *)
(* polymorphic compare should just work here *)
let rec dedupe_list = function
  | [] -> []
  | x::l -> x::(dedupe_list (List.filter (fun x' -> x <> x') l))

let get_first_element = function
  | Singleton site -> site
  | Cycle x::_ -> x
  | Cycle [] -> raise EmptyCycle

let first_dupe_callstring l =
  let combine (first_dupe, current_set) element =
    let first_element = get_first_element element
    begin match first_dupe with
    | None ->
      if Set.mem current_set first_element then
        (Some first_element, current_set)
      else
        (None, Set.add current_set first_element)
    | Some x -> (Some x, current_set)
    end
  in
  fst (List.fold_left combine Set.empty l)

exception NoDupeFound

(* Takes a walk of callstring elements and a vertex
   which is assumed to be the first duplicate element
   and returns the cycle that begins with that duplicate
   element.
   e.g. cycle_list ([a;b;c;a;b;c], a) -> [a;b;c]
   Note: We should have a unit test for this.
 *)
let cycle_list callstring_list v_dupe =
  let rec clear_start = function
    | x::l when get_first_element x = v_dupe -> l
    | _::l -> clear_start l
    | [] -> raise NoDupeFound
  let dupe_start = clear_start callstring_list in
  let rec collect_cycle collected = function
    | x::l when get_first_element x = v_dupe -> collected
    | x::l -> x::(collect_cycle l)
    | [] -> raise NoDupeFound (* didn't find the other element *)
  in
  List.rev (collect_cycle [] dupe_start)

let rec prefix_matches l cycle_l =
  match (l, cycle_l) with
  | ((Singleton x)::l, (Singleton x')::l') ->
    if x = x' then prefix_matches l l' else false
  | ([], _::_) -> false
  | (_::_, []) -> false
  | ([], []) -> true

exception NotMatching

let rec drop_cycle l cycle_l =
  match (l, cycle_l) with
  | (x'::l', x''::l'') ->
    if x' <> x'' then
      raise NotMatching
    else
      drop_cycle l' l''
  | (_, []) -> l
  | _ -> raise NotMatching

(* replace runs of singletons in l with Cycle (cycle_l) *)
let rec replace_cycles l cycle_l =
  let rec replace_cycles' l =
    match l with
    | [] -> []
    | x::l' ->
      if prefix_matches (x::l') cycle_l then
        let dropped = (drop_cycle_prefix l' cycle_l) |> replace_cycles' in
        (Cycle cycle_l)::dropped
      else
        x::(replace_cycles' l)
  in
  replace_cycles' l

(* takes a walk of callsites (ints) from a graph and makes a callstring *)
let callstring_of_callsite_list l =
  let callstring_of_callsite_list' l' =
    begin match first_dupe_callstring l' with
    | None -> l' (* no duplicates => no cycles remaining *)
    | Some v_dupe ->
      let cycle_l = cycle_list l' v_dupe in
      (* replace cycles with one Cycle node *)
      let cycles_replaced = replace_cycles l' cycle_l in
      dedupe_list cycles_replaced
      |> callstring_of_callsite_list'
    end
  in
  List.map (fun x -> Singleton x) l
  |> callstring_of_callsite_list'
  |> dedupe_list

exception Unimplemented
let make_map callstring_list = raise Unimplemented

(* Given a program, return a table m where m maps from a function to
 * the acyclic call string.
 *)
let astrings p = p |> all_calls |> callstring_of_callsite_list |> make_map

(* Given a call string table and a root r, generate a call string tree. *)
let cstree_of_table = ()

(* Given a program and a root r, generate a call string tree. *)
let cstree_of_program = ()
