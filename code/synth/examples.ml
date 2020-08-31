open MyStdLib
open Lang

type t =
  | ExMap of t * t
  | Vals of ParseTree.t list
[@@deriving eq, hash, ord, show]
