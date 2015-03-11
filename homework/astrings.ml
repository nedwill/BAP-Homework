open Core_kernel.Std
open Bap.Std
open Program_visitor
open Callstrings

let main p =
  let cs = callstrings p "main" in
  let _ = Seq.iter cs ~f:print_endline in
  p

let () = register main
