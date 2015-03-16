open Core_kernel.Std
open Bap.Std
open Program_visitor
open Callstrings

let string_of_call_string_element = function
  | Singleton x -> "Singleton (" ^ Int.to_string x ^ ")"
  | Cycle l -> "Cycle (" ^ (List.map ~f:Int.to_string l |> String.concat ~sep:", ") ^ ")"

let string_of_astring : astring -> string =
  List.to_string ~f:(string_of_call_string_element)

let print_astring_table : astring list table -> unit =
  let () = printf "print_astring_table called!\n%!" in
  Table.iteri ?start:None ?until:None ~f:(
    fun mem csl ->
      let addr_string = Memory.min_addr mem |> Bitvector.to_string in
      let out = List.map ~f:string_of_astring csl |> String.concat ~sep:"\n" in
      begin printf "sub_%s:\n%s\n%!" addr_string out end
  )

let main p =
  let ast_table = astrings p in
  let () = print_astring_table ast_table in
  p

let () = register main
