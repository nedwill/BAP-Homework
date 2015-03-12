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

exception Unexpected
exception SizeError

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
  let g cs_list next_possible =
    Set.fold next_possible (grow_list cs_list)
  let f cs = 
    let cs_list = list_of_callstring cs in
    let (_, _, last_dst) = List.end cs_list in (* exn if empty? *)
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

(* Given a program, return a table m where m maps from a function to
 * the acyclic call string.
 *)
let astrings = ()

(* Given a call string table and a root r, generate a call string tree. *)
let cstree_of_table = ()

(* Given a program and a root r, generate a call string tree. *)
let cstree_of_program = ()
