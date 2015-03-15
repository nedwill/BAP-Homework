open Core_kernel.Std
open Bap.Std
open Program_visitor
open Callstrings

let main p =
  output_callstring_graph p "main" "graph.dot";
  p

let () = register main
