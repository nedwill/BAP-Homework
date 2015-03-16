open Core_kernel.Std
open Bap.Std
open Program_visitor

(* Tree Types *)
type func = string
type call = int * func * func
type node = Terminal of call | Recursive of call | External of call | Node of call * node seq | Root of func * node seq

(* Astring Types *)
type call_site = int
type astring_element =
  | Singleton of call_site
  | Cycle of call_site list
type astring = astring_element list

(* User-Defined Exceptions *)
exception EmptyList
exception EmptyCycle
exception NoI
exception NotOneI
exception NoDupeFound
exception NotMatching

let calls syms insns =
  Seq.concat_map insns ~f:(
    fun (_mem, insn) ->
      let visitor =
        object inherit [string seq] Bil.visitor
          method! enter_int addr calls =
            if in_jmp then
              match Table.find_addr syms addr with
              | None -> calls
              | Some (mem, dst) ->
                if Addr.(Memory.min_addr mem = addr) then
                  Seq.cons dst calls
                else calls
            else calls
        end
      in visitor#run (Insn.bil insn) Seq.empty)

(* Call Tree *)
let all_calls p =
  let string_tab = Table.mapi p.symbols ~f:(
      fun mem src ->
        Seq.map (calls p.symbols (Disasm.insns_at_mem p.program mem)) ~f:(
          fun dst -> (src, dst))) in (* include mem for src to get mapping *)
  let flattened = Seq.concat_map ~f:snd (Table.to_sequence string_tab) in
  Seq.mapi flattened ~f:(fun i (src, dst) -> (i, src, dst))

(* Recursive helper function to build the callstring tree *)
let rec callstring_tree_from root calls call =
  let rootcalls = Seq.filter calls ~f:(
      fun (_i, src, _dst) -> (src = root)) in
  let children = (Seq.map rootcalls ~f:(
      fun (i, src, dst) ->
        let nextcall = (i,src,dst) in
        if src = dst then (Recursive nextcall) else
          (callstring_tree_from dst calls (Some nextcall)))) in
  match call with
  (* If we're not reached from a call, then we're the root *)
  | None -> Root (root, children)
  | Some c -> if Seq.is_empty children then Terminal(c) else Node (c, children)

let callstring_tree p root = callstring_tree_from root (all_calls p) None

module CallstringGraph = struct
  type t = node

  module V = struct
    type t = node * int list
  end

  module E = struct
    type t = V.t * V.t
    let src = fst
    let dst = snd
  end

  (* Get the callnumber for a given node if it exists *)
  let get_callnum t =
    match t with
    | Root (_, _) -> None
    | Node ((i, _src, _dst), _)
    | Recursive (i, _src, _dst)
    | External (i, _src, _dst)
    | Terminal (i, _src, _dst) -> Some i

  (* Recursive iterator over the ADT. Builds up the callstring in the calls *)
  let rec iter_v f calls t =
    let cn = get_callnum t in
    let calls =
      begin match cn with
        | Some i -> i :: calls
        | None -> calls
      end
    in
    (f (t, calls); match t with
      | Root (_, children) -> f (t, []); Seq.iter children ~f:(iter_v f [])
      | Node (_, children) -> Seq.iter children ~f:(iter_v f (calls))
      | _ -> ())

  let iter_vertex f t = iter_v f [] t

  (* Recursive iterator over the ADT *)
  let rec iter_e f calls t =
    let cn = get_callnum t in
    let calls =
      begin match cn with
        | Some i -> i :: calls
        | None -> calls
      end
    in
    match t with
    | Node (_, children) | Root (_, children)-> Seq.iter children ~f:(
        fun next ->
          let nextnum = get_callnum next in
          let nextcalls =
            begin match nextnum with
              | Some i -> i :: calls
              | None -> calls
            end
          in
          f ((t, calls), (next, nextcalls)); iter_e f (calls) next; ())
    | _ -> ()

  let iter_edges_e f t = iter_e f [] t

  let graph_attributes _ = []

  let quote = sprintf "%S"

  (* Proper labels for the vertices *)
  let vertex_label (v, _call_string) =
    match v with
    | Terminal (i, _src, dst) -> sprintf "T(%s:%d)" dst i
    | Recursive(i, src, dst) -> sprintf "R(%s:%d,%s)" src i dst
    | External(i, _src, dst) -> sprintf "E(%s:%d)" dst i
    | Node ((i, _src, dst), _) -> sprintf "%s:%d" dst i
    | Root (func, _calls) -> func

  open Graph.Graphviz.CommonAttributes
  let vertex_attributes v = [`Label (vertex_label v)]

  (* Give vertex a unique name based on the call_string *)
  let vertex_name (v, call_string) =
    quote (vertex_label (v, call_string) ^ List.fold call_string ~init:"" ~f:(sprintf "%s %d"))

  let default_vertex_attributes _ = []

  let get_subgraph _ = None

  let default_edge_attributes _ = []
  let edge_attributes _ = []
end

let output_callstring_graph p root outfile =
  let call_tree = callstring_tree p root in
  let module Dot = Graph.Graphviz.Dot (CallstringGraph) in
  Out_channel.with_file outfile ~f:(fun out -> Dot.output_graph out call_tree)

(* Astrings *)
let all_calls_mem p =
  let string_tab = Table.mapi p.symbols ~f:(
      fun mem src ->
        Seq.map (calls p.symbols (Disasm.insns_at_mem p.program mem)) ~f:(
          fun dst -> (mem, src, dst))) in (* include mem for src to get mapping *)
  let flattened = Seq.concat_map ~f:snd (Table.to_sequence string_tab) in
  Seq.mapi flattened ~f:(fun i (src_mem, src, dst) -> (i, src_mem, src, dst))

let rec end_of_list = function
  | [] -> raise EmptyList
  | [x] -> x
  | _::l -> end_of_list l

(* given a graph g and a callsite v, what is the destination of that call? *)
let get_target_dst g v =
  match List.filter ~f:(fun (i, _src_mem, _src, _dst) -> i = v) g with
  | [] -> raise NoI
  | [(_i, _src_mem, _src, dst)] -> dst (* map as seq :/ *)
  | _::_ -> raise NotOneI

(* out-neighbors of v in g *)
let neighborhood g v = (* could filter_map *)
  let target_dst = get_target_dst g v in
  List.filter ~f:(fun (_i, _src_mem, src, _dst) -> src = target_dst) g
  |> List.map ~f:(fun (i, _src_mem, _src, _dst) -> i)

(* gives all walks up to length k in digraph G starting from vertex v *)
let rec paths g =
  let nbrhood = neighborhood g v in
  List.map ~f:(fun nbr -> (paths g (k-1) nbr)) nbrhood
  |> List.concat
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

let rec prefix_matches l cycle_l =
  match (l, cycle_l) with
  | ((Singleton x)::l, x'::l') ->
    if x = x' then prefix_matches l l' else false
  | ((Cycle _::_), _::_) -> false
  | ([], _::_) -> false
  | (_::_, []) -> false
  | ([], []) -> true

let rec drop_cycle_prefix l cycle_l =
  match (l, cycle_l) with
  | ((Singleton x')::l', x''::l'') ->
    if x' <> x'' then
      raise NotMatching
    else
      drop_cycle_prefix l' l''
  | (_, []) -> l
  | _ -> raise NotMatching

(* replace runs of singletons in l with Cycle (cycle_l) *)
let replace_cycles l cycle_l =
  let rec replace_cycles' l =
    match l with
    | [] -> []
    | x::l' ->
      if prefix_matches (x::l') cycle_l then
        let dropped = drop_cycle_prefix l' cycle_l
                                |> replace_cycles' in (* careful, not tail recursive *)
        (Cycle cycle_l)::dropped
      else
        x::(replace_cycles' l')
  in
  replace_cycles' l

(* takes a walk of callsites (ints) from a graph and makes a callstring list *)
let callstring_of_callsite_list l =
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

let find_srcmem_dst g bts =
  List.find_exn g ~f:(fun (_i, _src_mem, src, _dst) -> src = bts)
  |> (fun (_i, src_mem, _src, _dst) -> src_mem)

(* bap doesn't have Table.of_alist_exn or Table.of_alist_fold :( *)
(* Take a ('a, 'b) list where the keys are not necessarily unique
   and make a ('a, 'b list) list where the keys are unique and all
   values seen for a given k are in placed in a list. *)
(* For example, compress [(3, 5); (5, 6); (3, 4)] -> [(3, [5; 4]), (5, [6])] *)
let rec compress g = function
  | [] -> []
  | (i, lst)::l ->
    let (matching, not_matching) = List.partition_tf ~f:(fun (i', _) -> i = i') l in
    let all_i_lists = List.fold ~f:(fun l' (_i, lst') -> lst'::l') ~init:[lst] matching in
    (find_srcmem_dst g i, all_i_lists)::(compress g not_matching)

let table_of_list = List.fold ~init:Table.empty ~f:(fun tb (x,y) -> Table.add tb x y |> ok_exn)

(* Given an astring and the callsite graph, determine the destination
   of the last callsite.
 *)
let get_astring_dest astr g =
  end_of_list astr (* get last element of astring *)
  |> get_first_element (* get first element (if cycle, then first element) *)
  |> get_target_dst g (* get the target of the call *)

(* Given a list of astrings, make a map from each function to the list of
   all acyclic call strings for that function.
 *)
let make_map g astr_list =
  List.map ~f:(fun astr -> (get_astring_dest astr g, x)) astr_list
  |> compress g
  |> table_of_list

(* Given a path l, find all subpaths. *)
let get_subpaths_one_path l =
  let rec subpaths l a =
    begin match l with
      | [] -> a (* don't include empty path *)
      | _::l' -> subpaths l' (l::a)
    end
  in
  subpaths l [] |> List.concat

let get_subpaths_list l =
  List.map l ~f:get_subpaths_one_path |> dedupe_list

let get_astrings ~max_path_length (i, _src_mem, _src, _dst) =
  paths g max_path_length i
  |> List.map ~f:callstring_of_callsite_list
  |> get_subpaths_list

(* Given a program, return a table m where m maps from a function to
 * the acyclic call string.
*)
let astrings p =
  let g = p |> all_calls_mem |> Seq.to_list in
  let max_path_length = 2*(List.length g) in
  List.map ~f:(get_astrings ~max_path_length) g
  |> List.concat
  |> dedupe_list
  |> make_map g
