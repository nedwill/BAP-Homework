open Core_kernel.Std
open Bap.Std
open Program_visitor
open Callstrings

(* use these to store callstring as an int *)
let callstring_of_list = ()
let list_of_callstring = ()

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

let main p =
  let cs = callstrings p "main" in
  let _ = Seq.iter cs ~f:print_endline in
  p

let () = register main
