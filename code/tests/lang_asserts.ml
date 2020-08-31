open MyStdLib
open OUnitPlusPlus
open Lang

let assert_grammar_equal
    (expected:Grammar.t)
    (actual:Grammar.t) =
  assert_equal
    ~printer:Grammar.show
    ~cmp:Grammar.compare
    expected
    actual

let assert_grammar_list_unordered_equal
    (expected:Grammar.t list)
    (actual:Grammar.t list) =
  assert_equal
    ~printer:(string_of_list Grammar.show)
    ~cmp:(compare_list_as_multisets ~cmp:Grammar.compare)
    expected
    actual

let assert_probabilistic_grammar_equal
    (expected:ProbabilisticGrammar.t)
    (actual:ProbabilisticGrammar.t) =
  assert_equal
    ~printer:ProbabilisticGrammar.show
    ~cmp:ProbabilisticGrammar.compare
    expected
    actual
