open MyStdLib
open OUnitPlusPlus
open Synth
open Lang

let assert_converter_equal
    (expected:Converter.t)
    (actual:Converter.t)
  : unit =
  assert_equal
    ~printer:(fun c -> Converter.show c ^ " " ^ (string_of_int (Converter.size c)))
    ~cmp:Converter.compare
    expected
    actual

let assert_string_bool_list_equal
    (expected:(string * (bool list)))
    (actual:(string * (bool list)))
  : unit =
  assert_equal
    ~printer:(string_of_pair ident (string_of_list Bool.to_string))
    ~cmp:(pair_compare (String.compare) (compare_list ~cmp:Bool.compare))
    expected
    actual

