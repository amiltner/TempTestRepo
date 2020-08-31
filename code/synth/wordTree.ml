open MyStdLib
open Lang

type t =
  | Choice of int * t
  | Concat of t list
