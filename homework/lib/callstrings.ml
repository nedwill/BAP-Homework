open Core_kernel.Std
open Bap.Std
open Program_visitor

type func = string
type call = int * func * func
type node = Terminal of call | Recursive of call | External of call | Node of call * node seq | Root of func * node seq

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
    let calls = (match cn with
      | Some i -> i :: calls
      | None -> calls) in
    (f (t, calls); match t with
    | Root (_, children) -> f (t, []); Seq.iter children ~f:(iter_v f [])
    | Node (_, children) -> Seq.iter children ~f:(iter_v f (calls))
    | _ -> ())

  let iter_vertex f t = iter_v f [] t

  (* Recursive iterator over the ADT *)
  let rec iter_e f calls t =
    let cn = get_callnum t in
    let calls = (match cn with
      | Some i -> i :: calls
      | None -> calls) in
    match t with
    | Node (_, children) | Root (_, children)-> Seq.iter children ~f:(
      fun next ->
        let nextnum = get_callnum next in
        let nextcalls = (match nextnum with
        | Some i -> i :: calls
        | None -> calls) in
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
