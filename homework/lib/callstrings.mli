open Bap.Std
open Program_visitor

type func = string
type call = int * func * func
type node = Terminal of call | Recursive of call | External of call | Node of call * node seq | Root of func * node seq

(* val acyclic_callstrings : project -> string -> string seq *)
val callstring_tree : project -> string -> node
val output_callstring_graph : project -> string -> string -> unit
