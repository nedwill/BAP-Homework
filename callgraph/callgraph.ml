open Core_kernel.Std
open Bap.Std
open Program_visitor

(*
let main project =
    (* print_endline "hello, BAP"; *)
    Table.iter project.symbols ~f:print_endline;
    project
*)

module Callgraph = struct
  type t = project
  module V = struct
    type t = string
  end
  module E = struct
    type t = string * string
    let src = fst
    let dst = snd
  end
  let iter_vertex f t =
    Table.iter t.symbols ~f
  let iter_edges_e f t =
    Table.iteri t.symbols ~f:(fun mem src -> 
        Disasm.insns_at_mem t.program mem |>
        Seq.iter ~f:(fun (_mem, insn) -> Bil.iter (object
                        inherit [unit] Bil.visitor
                        method! enter_int addr () =
                          if in_jmp then
                            match Table.find_addr t.symbols addr with
                            | None -> ()
                            | Some (mem, dst) ->
                              if Addr.(Memory.min_addr mem = addr) (*jumped to another func *)
                              then f (src, dst)
                      end) (Insn.bil insn))
      )
  let graph_attributes _ = []
  let default_vertex_attributes _ = []
  let quote = sprintf "%S"
  let vertex_name = quote
  let vertex_attributes _ = []
  let get_subgraph _ = None
  let default_edge_attributes _ = []
  let edge_attributes _ = []
end

let main p =
  let module Dot = Graph.Graphviz.Dot (Callgraph) in
  Out_channel.with_file "callgraph.dot" ~f:(fun out -> Dot.output_graph out p);
  p (* return project *)

let () = register main

