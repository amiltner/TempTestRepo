open MyStdLib

module Context = struct
  type t = MapOf(Id)(PairOf(ParseTree)(Examples))
end
