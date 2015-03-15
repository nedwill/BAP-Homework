open Bap.Std
open Program_visitor

type call_site = int

type astring_element =
  | Singleton of call_site
  | Cycle of call_site list

type astring = astring_element list

val callstrings : project -> string -> string seq

val astrings : project -> astring list table
