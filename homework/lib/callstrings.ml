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
  Seq.mapi flattened ~f:(fun i (addr, src, dst) -> (i, addr, src, dst))

let callstrings p root = Seq.empty
