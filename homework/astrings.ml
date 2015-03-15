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
  Table.iteri ~f:(
    fun mem csl ->
      let addr_string = Memory.min_addr mem |> Bitvector.to_string in
      let out = List.map ~f:string_of_astring csl |> String.concat ~sep:"\n" in
      Printf.printf "sub_%s:\n%s\n" addr_string out
  )

let main p =
  let () = astrings p |> print_astring_table in
  p

let () = register main
