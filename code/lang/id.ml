open MyStdLib

type t = Id of string
[@@deriving bin_io, eq, hash, ord, sexp, show]

let mk_prime (Id x : t) : t = Id (x ^ "'")

let create (s:string) : t = Id s

let from_int (i:int) : t = Id ("v" ^ (string_of_int i))
