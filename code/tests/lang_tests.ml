open MyStdLib
open Lang
open Lang_asserts
open OUnitPlusPlus

(* nullable begin *)
let from_kvp_list_exn = Grammar.from_kvp_list_exn (Grammar.Production.mk_nonterminal (Id.create "S"))
let check_nullable_empty _ =
  assert_bool_equal
    true
    (Automata.nullable
       (Automata.from_grammar
          (from_kvp_list_exn
             [((Id.create "S"),(Grammar.Production.mk_terminal ""))])))

let check_nullable_empty_lang _ =
  assert_bool_equal
    false
    (Automata.nullable
       (Automata.from_grammar
          (from_kvp_list_exn
             [((Id.create "S"),(Grammar.Production.empty))])))

let check_nullable_nonempty _ =
  assert_bool_equal
    false
    (Automata.nullable
       (Automata.from_grammar
          (from_kvp_list_exn
             [((Id.create "S"),(Grammar.Production.mk_terminal "x"))])))

let check_nullable_disjuncted_left _ =
  assert_bool_equal
    true
    (Automata.nullable
       (Automata.from_grammar
          (from_kvp_list_exn
             [((Id.create "S"),
               (Grammar.Production.mk_or
                  (Grammar.Production.mk_terminal "")
                  (Grammar.Production.mk_terminal "x"))
               )])))

let check_nullable_disjuncted_right _ =
  assert_bool_equal
    true
    (Automata.nullable
       (Automata.from_grammar
          (from_kvp_list_exn
             [((Id.create "S"),
               (Grammar.Production.mk_or
                  (Grammar.Production.mk_terminal "x")
                  (Grammar.Production.mk_terminal ""))
              )])))

let check_nullable_disjuncted_notnull _ =
  assert_bool_equal
    false
    (Automata.nullable
       (Automata.from_grammar
          (from_kvp_list_exn
             [((Id.create "S"),
               (Grammar.Production.mk_or
                  (Grammar.Production.mk_terminal "x")
                  (Grammar.Production.mk_terminal "y"))
              )])))

let check_nullable_recursive_infinite _ =
  assert_bool_equal
    false
    (Automata.nullable
       (Automata.from_grammar
          (from_kvp_list_exn
             [((Id.create "S"),
               (Grammar.Production.mk_concat
                  (Grammar.Production.mk_terminal "x")
                  (Grammar.Production.mk_nonterminal (Id.create "S")))
              )])))

let check_nullable_complex_true _ =
  assert_bool_equal
    true
    (Automata.nullable
       (Automata.from_grammar
          (from_kvp_list_exn
             [((Id.create "S"),
               (Grammar.Production.mk_concat
                  (Grammar.Production.mk_nonterminal (Id.create "U"))
                  (Grammar.Production.mk_nonterminal (Id.create "T"))))
             ;((Id.create "T"),
               (Grammar.Production.mk_concat
                  (Grammar.Production.mk_terminal "")
                  (Grammar.Production.mk_nonterminal (Id.create "U"))))
             ;((Id.create "U"),
               (Grammar.Production.mk_terminal ""))
             ])))

let check_nullable_complex_false _ =
  assert_bool_equal
    false
    (Automata.nullable
       (Automata.from_grammar
          (from_kvp_list_exn
             [((Id.create "S"),
               (Grammar.Production.mk_concat
                  (Grammar.Production.mk_nonterminal (Id.create "U"))
                  (Grammar.Production.mk_nonterminal (Id.create "T"))))
             ;((Id.create "T"),
               (Grammar.Production.mk_concat
                  (Grammar.Production.mk_terminal "")
                  (Grammar.Production.mk_nonterminal (Id.create "U"))))
             ;((Id.create "U"),
               (Grammar.Production.mk_terminal "T"))
             ])))

let nullable_suite =
  "nullable Unit Tests" >:::
  ["check_nullable_empty" >:: check_nullable_empty
  ;"check_nullable_nonempty" >:: check_nullable_nonempty
  ;"check_nullable_empty_lang" >:: check_nullable_empty_lang
  ;"check_nullable_disjuncted_left" >:: check_nullable_disjuncted_left
  ;"check_nullable_disjuncted_right" >:: check_nullable_disjuncted_right
  ;"check_nullable_disjuncted_notnull" >:: check_nullable_disjuncted_notnull
  ;"check_nullable_recursive_infinite" >:: check_nullable_recursive_infinite
  ;"check_nullable_complex_true" >:: check_nullable_complex_true
  ;"check_nullable_complex_false" >:: check_nullable_complex_false
  ]

let _ = run_test_tt_main nullable_suite
(* nullable end *)


(* accepts begin *)
let check_accepts_empty_empty _ =
  assert_bool_equal
    true
    (Automata.accepts
       (Automata.from_grammar
          (from_kvp_list_exn
             [((Id.create "S"),(Grammar.Production.mk_terminal ""))]))
       "")

let check_accepts_empty_nonempty _ =
  assert_bool_equal
    false
    (Automata.accepts
       (Automata.from_grammar
          (from_kvp_list_exn
             [((Id.create "S"),(Grammar.Production.mk_terminal ""))]))
       "c")

let check_accepts_singleton_singleton _ =
  assert_bool_equal
    true
    (Automata.accepts
       (Automata.from_grammar
          (from_kvp_list_exn
             [((Id.create "S"),(Grammar.Production.mk_terminal "abc"))]))
       "abc")

let check_accepts_singleton_empty _ =
  assert_bool_equal
    false
    (Automata.accepts
       (Automata.from_grammar
          (from_kvp_list_exn
             [((Id.create "S"),(Grammar.Production.mk_terminal "abc"))]))
       "")

let check_accepts_iteration_left_empty _ =
  assert_bool_equal
    true
    (Automata.accepts
       (Automata.from_grammar
          (from_kvp_list_exn
             [((Id.create "S")
              ,(Grammar.Production.mk_or
                  (Grammar.Production.mk_terminal "")
                  (Grammar.Production.mk_concat
                     (Grammar.Production.mk_nonterminal (Id.create "S"))
                     (Grammar.Production.mk_terminal "s"))
               ))]))
       "")

let check_accepts_iteration_left_single _ =
  assert_bool_equal
    true
    (Automata.accepts
       (Automata.from_grammar
          (from_kvp_list_exn
             [((Id.create "S")
              ,(Grammar.Production.mk_or
                  (Grammar.Production.mk_terminal "")
                  (Grammar.Production.mk_concat
                     (Grammar.Production.mk_terminal "s")
                     (Grammar.Production.mk_nonterminal (Id.create "S")))
               ))]))
       "s")

let check_accepts_iteration_left_many _ =
  assert_bool_equal
    true
    (Automata.accepts
       (Automata.from_grammar
          (from_kvp_list_exn
             [((Id.create "S")
              ,(Grammar.Production.mk_or
                  (Grammar.Production.mk_terminal "")
                  (Grammar.Production.mk_concat
                     (Grammar.Production.mk_terminal "s")
                     (Grammar.Production.mk_nonterminal (Id.create "S")))
               ))]))
       "ssssss")

let check_accepts_iteration_right_empty _ =
  assert_bool_equal
    true
    (Automata.accepts
       (Automata.from_grammar
          (from_kvp_list_exn
             [((Id.create "S")
              ,(Grammar.Production.mk_or
                  (Grammar.Production.mk_terminal "")
                  (Grammar.Production.mk_concat
                     (Grammar.Production.mk_nonterminal (Id.create "S"))
                     (Grammar.Production.mk_terminal "s"))
               ))]))
       "")

let check_accepts_iteration_right_single _ =
  assert_bool_equal
    true
    (Automata.accepts
       (Automata.from_grammar
          (from_kvp_list_exn
             [((Id.create "S")
              ,(Grammar.Production.mk_or
                  (Grammar.Production.mk_terminal "")
                  (Grammar.Production.mk_concat
                     (Grammar.Production.mk_terminal "s")
                     (Grammar.Production.mk_nonterminal (Id.create "S")))
               ))]))
       "s")

let check_accepts_iteration_right_many _ =
  assert_bool_equal
    true
    (Automata.accepts
       (Automata.from_grammar
          (from_kvp_list_exn
             [((Id.create "S")
              ,(Grammar.Production.mk_or
                  (Grammar.Production.mk_terminal "")
                  (Grammar.Production.mk_concat
                     (Grammar.Production.mk_terminal "s")
                     (Grammar.Production.mk_nonterminal (Id.create "S")))
               ))]))
       "ssssss")

let check_accepts_iteration_left_wrong _ =
  assert_bool_equal
    false
    (Automata.accepts
       (Automata.from_grammar
          (from_kvp_list_exn
             [((Id.create "S")
              ,(Grammar.Production.mk_or
                  (Grammar.Production.mk_terminal "")
                  (Grammar.Production.mk_concat
                     (Grammar.Production.mk_terminal "s")
                     (Grammar.Production.mk_nonterminal (Id.create "S")))
               ))]))
       "t")

let check_accepts_iteration_left_many_wrong _ =
  assert_bool_equal
    false
    (Automata.accepts
       (Automata.from_grammar
          (from_kvp_list_exn
             [((Id.create "S")
              ,(Grammar.Production.mk_or
                  (Grammar.Production.mk_terminal "")
                  (Grammar.Production.mk_concat
                     (Grammar.Production.mk_terminal "s")
                     (Grammar.Production.mk_nonterminal (Id.create "S")))
               ))]))
       "sssssst")

let accepts_suite =
  "accepts Unit Tests" >:::
  ["check_accepts_empty_empty" >:: check_accepts_empty_empty
  ;"check_accepts_empty_nonempty" >:: check_accepts_empty_nonempty
  ;"check_accepts_singleton_singleton" >:: check_accepts_singleton_singleton
  ;"check_accepts_singleton_empty" >:: check_accepts_singleton_empty
  ;"check_accepts_iteration_left_empty" >:: check_accepts_iteration_left_empty
  ;"check_accepts_iteration_left_single" >:: check_accepts_iteration_left_single
  ;"check_accepts_iteration_left_many" >:: check_accepts_iteration_left_many
  ;"check_accepts_iteration_right_empty" >:: check_accepts_iteration_right_empty
  ;"check_accepts_iteration_right_single" >:: check_accepts_iteration_right_single
  ;"check_accepts_iteration_right_many" >:: check_accepts_iteration_right_many
  ;"check_accepts_iteration_left_wrong" >:: check_accepts_iteration_left_wrong
  ;"check_accepts_iteration_left_many_wrong" >:: check_accepts_iteration_left_many_wrong
  ]

let _ = run_test_tt_main accepts_suite
(* accepts end *)

(* parse begin *)
let check_parse_empty_empty _ =
  assert_bool_list_option_equal
    (Some [])
    (Automata.parse
       (Automata.from_grammar
          (from_kvp_list_exn
             [((Id.create "S"),(Grammar.Production.mk_terminal ""))]))
       "")

let check_parse_singleton_singleton _ =
  assert_bool_list_option_equal
    (Some [])
    (Automata.parse
       (Automata.from_grammar
          (from_kvp_list_exn
             [((Id.create "S"),(Grammar.Production.mk_terminal "abc"))]))
       "abc")

let check_parse_iteration_left_empty _ =
  assert_bool_list_option_equal
    (Some [true])
    (Automata.parse
       (Automata.from_grammar
          (from_kvp_list_exn
             [((Id.create "S")
              ,(Grammar.Production.mk_or
                  (Grammar.Production.mk_terminal "")
                  (Grammar.Production.mk_concat
                     (Grammar.Production.mk_nonterminal (Id.create "S"))
                     (Grammar.Production.mk_terminal "s"))
               ))]))
       "")

let check_parse_iteration_left_single _ =
  assert_bool_list_option_equal
    (Some [false;true])
    (Automata.parse
       (Automata.from_grammar
          (from_kvp_list_exn
             [((Id.create "S")
              ,(Grammar.Production.mk_or
                  (Grammar.Production.mk_terminal "")
                  (Grammar.Production.mk_concat
                     (Grammar.Production.mk_terminal "s")
                     (Grammar.Production.mk_nonterminal (Id.create "S")))
               ))]))
       "s")

let check_parse_iteration_left_many _ =
  assert_bool_list_option_equal
    (Some [false;false;false;false;false;false;true])
    (Automata.parse
       (Automata.from_grammar
          (from_kvp_list_exn
             [((Id.create "S")
              ,(Grammar.Production.mk_or
                  (Grammar.Production.mk_terminal "")
                  (Grammar.Production.mk_concat
                     (Grammar.Production.mk_terminal "s")
                     (Grammar.Production.mk_nonterminal (Id.create "S")))
               ))]))
       "ssssss")

let check_parse_iteration_right_empty _ =
  assert_bool_list_option_equal
    (Some [true])
    (Automata.parse
       (Automata.from_grammar
          (from_kvp_list_exn
             [((Id.create "S")
              ,(Grammar.Production.mk_or
                  (Grammar.Production.mk_terminal "")
                  (Grammar.Production.mk_concat
                     (Grammar.Production.mk_nonterminal (Id.create "S"))
                     (Grammar.Production.mk_terminal "s"))
               ))]))
       "")

let check_parse_iteration_right_single _ =
  assert_bool_list_option_equal
    (Some [false;true])
    (Automata.parse
       (Automata.from_grammar
          (from_kvp_list_exn
             [((Id.create "S")
              ,(Grammar.Production.mk_or
                  (Grammar.Production.mk_terminal "")
                  (Grammar.Production.mk_concat
                     (Grammar.Production.mk_terminal "s")
                     (Grammar.Production.mk_nonterminal (Id.create "S")))
               ))]))
       "s")

let check_parse_iteration_right_many _ =
  assert_bool_list_option_equal
    (Some [false;false;false;false;false;false;true])
    (Automata.parse
       (Automata.from_grammar
          (from_kvp_list_exn
             [((Id.create "S")
              ,(Grammar.Production.mk_or
                  (Grammar.Production.mk_terminal "")
                  (Grammar.Production.mk_concat
                     (Grammar.Production.mk_terminal "s")
                     (Grammar.Production.mk_nonterminal (Id.create "S")))
               ))]))
       "ssssss")

let check_parse_iteration_very_hard _ =
  assert_bool_list_option_equal
    (Some [false;true;false;false;false;true;false;true;false;false;false;false;false;true;false;true;false;true;false;false;false;false;false;false;true])
    (Automata.parse
       (Automata.from_grammar
          (from_kvp_list_exn
             [((Id.create "S")
              ,(Grammar.Production.mk_or
                  (Grammar.Production.mk_terminal "")
                  (Grammar.Production.mk_concat
                     (Grammar.Production.mk_nonterminal (Id.create "T"))
                     (Grammar.Production.mk_nonterminal (Id.create "S")))))
             ;((Id.create "T")
              ,(Grammar.Production.mk_or
                  (Grammar.Production.mk_terminal "u")
                  (Grammar.Production.mk_terminal "v")))
             ]))
       "uvuuvvuuuvvv")

let parse_suite =
  "parse Unit Tests" >:::
  ["check_parse_empty_empty" >:: check_parse_empty_empty
  ;"check_parse_singleton_singleton" >:: check_parse_singleton_singleton
  ;"check_parse_iteration_left_empty" >:: check_parse_iteration_left_empty
  ;"check_parse_iteration_left_single" >:: check_parse_iteration_left_single
  ;"check_parse_iteration_left_many" >:: check_parse_iteration_left_many
  ;"check_parse_iteration_right_empty" >:: check_parse_iteration_right_empty
  ;"check_parse_iteration_right_single" >:: check_parse_iteration_right_single
  ;"check_parse_iteration_right_many" >:: check_parse_iteration_right_many
  ;"check_parse_iteration_very_hard" >:: check_parse_iteration_very_hard
  ]

let _ = run_test_tt_main parse_suite
(* parse end *)


(* probabilistic grammar builder begin *)
(*let check_build_empty _ =
  assert_probabilistic_grammar_equal
    (Probabilisticfrom_kvp_list_exn
       [((Id.create "S"),(ProbabilisticGrammar.Production.Terminal ""))])
    (ProbabilisticGrammarBuilder.build
       (from_kvp_list_exn
          [((Id.create "S"),(Grammar.Production.mk_terminal ""))])
       [])

let check_build_emptylang_left _ =
  assert_probabilistic_grammar_equal
    (Probabilisticfrom_kvp_list_exn
       [((Id.create "S"),
         (ProbabilisticGrammar.Production.mk_or
            (ProbabilisticGrammar.Production.empty)
            (ProbabilisticGrammar.Production.mk_terminal "a")
            0.))])
    (ProbabilisticGrammarBuilder.build
       (from_kvp_list_exn
          [((Id.create "S"),
            (Grammar.Production.mk_or
               (Grammar.Production.empty)
               (Grammar.Production.mk_terminal "a")))])
       [])

let check_build_emptylang_right _ =
  assert_probabilistic_grammar_equal
    (Probabilisticfrom_kvp_list_exn
       [((Id.create "S"),
         (ProbabilisticGrammar.Production.mk_or
            (ProbabilisticGrammar.Production.mk_terminal "a")
            (ProbabilisticGrammar.Production.empty)
            1.))])
    (ProbabilisticGrammarBuilder.build
       (from_kvp_list_exn
          [((Id.create "S"),
            (Grammar.Production.mk_or
               (Grammar.Production.mk_terminal "a")
               (Grammar.Production.empty)))])
       [])

let check_build_singleton _ =
  assert_probabilistic_grammar_equal
    (Probabilisticfrom_kvp_list_exn
       [((Id.create "S"),(ProbabilisticGrammar.Production.mk_terminal "abc"))])
    (ProbabilisticGrammarBuilder.build
       (from_kvp_list_exn
          [((Id.create "S"),(Grammar.Production.mk_terminal "abc"))])
       [])

let check_build_choice_noex _ =
  assert_probabilistic_grammar_equal
    (Probabilisticfrom_kvp_list_exn
       [((Id.create "S")
        ,(ProbabilisticGrammar.Production.mk_or
            (ProbabilisticGrammar.Production.mk_terminal "a")
            (ProbabilisticGrammar.Production.mk_terminal "b")
            0.5))])
    (ProbabilisticGrammarBuilder.build
       (from_kvp_list_exn
          [((Id.create "S")
           ,(Grammar.Production.mk_or
               (Grammar.Production.mk_terminal "a")
               (Grammar.Production.mk_terminal "b")))])
       [])

let check_build_choice_leftex _ =
  assert_probabilistic_grammar_equal
    (Probabilisticfrom_kvp_list_exn
       [((Id.create "S")
        ,(ProbabilisticGrammar.Production.mk_or
            (ProbabilisticGrammar.Production.mk_terminal "a")
            (ProbabilisticGrammar.Production.mk_terminal "b")
            1.0))])
    (ProbabilisticGrammarBuilder.build
       (from_kvp_list_exn
          [((Id.create "S")
           ,(Grammar.Production.mk_or
               (Grammar.Production.mk_terminal "a")
               (Grammar.Production.mk_terminal "b")))])
       ["a"])

let check_build_choice_rightex _ =
  assert_probabilistic_grammar_equal
    (Probabilisticfrom_kvp_list_exn
       [((Id.create "S")
        ,(ProbabilisticGrammar.Production.mk_or
            (ProbabilisticGrammar.Production.mk_terminal "a")
            (ProbabilisticGrammar.Production.mk_terminal "b")
            0.0))])
    (ProbabilisticGrammarBuilder.build
       (from_kvp_list_exn
          [((Id.create "S")
           ,(Grammar.Production.mk_or
               (Grammar.Production.mk_terminal "a")
               (Grammar.Production.mk_terminal "b")))])
       ["b"])

let check_build_choice_very_hard_single _ =
  assert_probabilistic_grammar_equal
    (Probabilisticfrom_kvp_list_exn
       [((Id.create "S")
        ,(ProbabilisticGrammar.Production.mk_or
            (ProbabilisticGrammar.Production.mk_terminal "")
            (ProbabilisticGrammar.Production.mk_concat
               (ProbabilisticGrammar.Production.mk_nonterminal (Id.create "T"))
               (ProbabilisticGrammar.Production.mk_nonterminal (Id.create "S")))
            (1. /. 13.)))
       ;((Id.create "T")
        ,(ProbabilisticGrammar.Production.mk_or
            (ProbabilisticGrammar.Production.mk_terminal "u")
            (ProbabilisticGrammar.Production.mk_terminal "v")
            0.5))
       ])
    (ProbabilisticGrammarBuilder.build
       (from_kvp_list_exn
          [((Id.create "S")
           ,(Grammar.Production.mk_or
               (Grammar.Production.mk_terminal "")
               (Grammar.Production.mk_concat
                  (Grammar.Production.mk_nonterminal (Id.create "T"))
                  (Grammar.Production.mk_nonterminal (Id.create "S")))))
          ;((Id.create "T")
           ,(Grammar.Production.mk_or
               (Grammar.Production.mk_terminal "u")
               (Grammar.Production.mk_terminal "v")))
          ])
       ["uvuuvvuuuvvv"])

let check_build_choice_very_hard_multiple _ =
  assert_probabilistic_grammar_equal
    (Probabilisticfrom_kvp_list_exn
       [((Id.create "S")
        ,(ProbabilisticGrammar.Production.mk_or
            (ProbabilisticGrammar.Production.mk_terminal "")
            (ProbabilisticGrammar.Production.mk_concat
               (ProbabilisticGrammar.Production.mk_nonterminal (Id.create "T"))
               (ProbabilisticGrammar.Production.mk_nonterminal (Id.create "S")))
            (2. /. 13.)))
       ;((Id.create "T")
        ,(ProbabilisticGrammar.Production.mk_or
            (ProbabilisticGrammar.Production.mk_terminal "u")
            (ProbabilisticGrammar.Production.mk_terminal "v")
            (13. /. 22.)))
       ])
    (ProbabilisticGrammarBuilder.build
       (from_kvp_list_exn
          [((Id.create "S")
           ,(Grammar.Production.mk_or
               (Grammar.Production.mk_terminal "")
               (Grammar.Production.mk_concat
                  (Grammar.Production.mk_nonterminal (Id.create "T"))
                  (Grammar.Production.mk_nonterminal (Id.create "S")))))
          ;((Id.create "T")
           ,(Grammar.Production.mk_or
               (Grammar.Production.mk_terminal "u")
               (Grammar.Production.mk_terminal "v")))
          ])
       ["uvuuvvuuuvvv";"uuuuu";"vuvu";"v"])

let build_probabilistic_grammar_suite =
  "parse Unit Tests" >:::
  ["check_build_empty" >:: check_build_empty
  ;"check_build_emptylang_left" >:: check_build_emptylang_left
  ;"check_build_emptylang_right" >:: check_build_emptylang_right
  ;"check_build_singleton" >:: check_build_singleton
  ;"check_build_choice_noex" >:: check_build_choice_noex
  ;"check_build_choice_leftex" >:: check_build_choice_leftex
  ;"check_build_choice_rightex" >:: check_build_choice_rightex
  ;"check_build_choice_very_hard_single" >:: check_build_choice_very_hard_single
  ;"check_build_choice_very_hard_multiple" >:: check_build_choice_very_hard_multiple
  ]

  let _ = run_test_tt_main build_probabilistic_grammar_suite*)
(* probabilistic grammar builder end *)


(* entropy begin *)
(*let check_entropy_iteration _ =
  assert_float_equal
    (3.6096405982971191)
    (ProbabilisticGrammar.entropy
       (Probabilisticfrom_kvp_list_exn
          [Id.create "S"
          ,ProbabilisticGrammar.Production.mk_or
              (ProbabilisticGrammar.Production.mk_terminal "")
              (ProbabilisticGrammar.Production.mk_concat
                 (ProbabilisticGrammar.Production.mk_terminal "a")
                 (ProbabilisticGrammar.Production.mk_nonterminal (Id.create "S")))
              0.2]))

let probabilistic_grammar_entropy_suite =
  "entropy Unit Tests" >:::
  ["check_entropy_iteration" >:: check_entropy_iteration
  ]

  let _ = run_test_tt_main probabilistic_grammar_entropy_suite*)
(* entropy end *)

let check_minify_remove_unnecessary _ =
  assert_grammar_equal
    (Grammar.initialize (Grammar.Production.mk_terminal "s"))
    (Grammar.minify
       (from_kvp_list_exn
          [(Id.create "S",Grammar.Production.mk_terminal "s")]))

let check_minify_remove_unnecessary_multiple _ =
  assert_grammar_equal
    (Grammar.initialize
       (Grammar.Production.mk_concat
          (Grammar.Production.mk_terminal "t")
          (Grammar.Production.mk_terminal "u")))
    (Grammar.minify
       (from_kvp_list_exn
          [(Id.create "S",
            Grammar.Production.mk_concat
              (Grammar.Production.mk_nonterminal (Id.create "T"))
              (Grammar.Production.mk_nonterminal (Id.create "U")))
           ;(Id.create "T",
             Grammar.Production.mk_terminal "t")
           ;(Id.create "U",
             Grammar.Production.mk_terminal "u")]))

let check_minify_remove_unnecessary_recursion _ =
  assert_grammar_equal
    (from_kvp_list_exn
       [(Id.create "S",
         Grammar.Production.mk_concat
           (Grammar.Production.mk_terminal "t")
           (Grammar.Production.mk_nonterminal (Id.create "S")))])
    (Grammar.minify
       (from_kvp_list_exn
          [(Id.create "S",
            Grammar.Production.mk_concat
              (Grammar.Production.mk_nonterminal (Id.create "T"))
              (Grammar.Production.mk_nonterminal (Id.create "S")))
          ;(Id.create "T",
            Grammar.Production.mk_terminal "t")]))

let check_minify_remove_unnecessary_doublerec _ =
  assert_grammar_equal
    (from_kvp_list_exn
       [(Id.create "S",
         Grammar.Production.mk_concat
           (Grammar.Production.mk_nonterminal (Id.create "S"))
           (Grammar.Production.mk_nonterminal (Id.create "S")))])
    (Grammar.minify
       (from_kvp_list_exn
          [(Id.create "S",
            Grammar.Production.mk_concat
              (Grammar.Production.mk_nonterminal (Id.create "T"))
              (Grammar.Production.mk_nonterminal (Id.create "S")))
          ;(Id.create "T",
            Grammar.Production.mk_nonterminal (Id.create "S"))]))

let check_minify_necessary_doublerec _ =
  assert_grammar_equal
    (from_kvp_list_exn
       [(Id.create "S",
         Grammar.Production.mk_concat
           (Grammar.Production.mk_nonterminal (Id.create "T"))
           (Grammar.Production.mk_nonterminal (Id.create "S")))
       ;(Id.create "T",
         Grammar.Production.mk_or
           (Grammar.Production.mk_nonterminal (Id.create "T"))
           (Grammar.Production.mk_nonterminal (Id.create "S")))])
    (Grammar.minify
       (from_kvp_list_exn
          [(Id.create "S",
            Grammar.Production.mk_concat
              (Grammar.Production.mk_nonterminal (Id.create "T"))
              (Grammar.Production.mk_nonterminal (Id.create "S")))
          ;(Id.create "T",
            Grammar.Production.mk_or
              (Grammar.Production.mk_nonterminal (Id.create "T"))
              (Grammar.Production.mk_nonterminal (Id.create "S")))]))

let minify_suite =
  "minify Unit Tests" >:::
  ["check_minify_remove_unnecessary" >:: check_minify_remove_unnecessary
  ;"check_minify_remove_unnecessary_multiple" >:: check_minify_remove_unnecessary_multiple
  ;"check_minify_remove_unnecessary_recursion" >:: check_minify_remove_unnecessary_recursion
  ;"check_minify_remove_unnecessary_doublerec" >:: check_minify_remove_unnecessary_doublerec
  ;"check_minify_necessary_doublerec" >:: check_minify_necessary_doublerec
  ]

let _ = run_test_tt_main minify_suite


let check_rewrites_easy_recursion_concat_left _ =
  assert_grammar_list_unordered_equal
    [from_kvp_list_exn
       [(Id.create "S"
        ,Grammar.Production.mk_concat
            (Grammar.Production.mk_concat
               (Grammar.Production.mk_nonterminal (Id.create "S"))
               (Grammar.Production.mk_terminal "s"))
            (Grammar.Production.mk_terminal "s"))]
    ;Grammar.from_kvp_list_exn
        (Grammar.Production.mk_concat
           (Grammar.Production.mk_nonterminal (Id.create "S"))
           (Grammar.Production.mk_terminal "s"))
        [(Id.create "S"
         ,Grammar.Production.mk_concat
             (Grammar.Production.mk_nonterminal (Id.create "S"))
             (Grammar.Production.mk_terminal "s"))]
    ]
    (Grammar.rewrites
       (from_kvp_list_exn
          [(Id.create "S"
           ,Grammar.Production.mk_concat
               (Grammar.Production.mk_nonterminal (Id.create "S"))
               (Grammar.Production.mk_terminal "s"))]))

let check_rewrites_easy_recursion_concat_right _ =
  assert_grammar_list_unordered_equal
    [from_kvp_list_exn
       [(Id.create "S"
        ,Grammar.Production.mk_concat
            (Grammar.Production.mk_terminal "s")
            (Grammar.Production.mk_concat
               (Grammar.Production.mk_terminal "s")
               (Grammar.Production.mk_nonterminal (Id.create "S"))))]
    ;Grammar.from_kvp_list_exn
        (Grammar.Production.mk_concat
           (Grammar.Production.mk_terminal "s")
           (Grammar.Production.mk_nonterminal (Id.create "S")))
        [(Id.create "S"
         ,Grammar.Production.mk_concat
             (Grammar.Production.mk_terminal "s")
             (Grammar.Production.mk_nonterminal (Id.create "S")))]
    ]
    (Grammar.rewrites
       (from_kvp_list_exn
          [(Id.create "S"
           ,Grammar.Production.mk_concat
               (Grammar.Production.mk_terminal "s")
               (Grammar.Production.mk_nonterminal (Id.create "S")))]))

let check_rewrites_easy_recursion_or_left _ =
  assert_grammar_list_unordered_equal
    [from_kvp_list_exn
       [(Id.create "S"
        ,Grammar.Production.mk_or
            (Grammar.Production.mk_or
               (Grammar.Production.mk_nonterminal (Id.create "S"))
               (Grammar.Production.mk_terminal "s"))
            (Grammar.Production.mk_terminal "s"))]
    ;Grammar.from_kvp_list_exn
        (Grammar.Production.mk_or
           (Grammar.Production.mk_nonterminal (Id.create "S"))
           (Grammar.Production.mk_terminal "s"))
        [(Id.create "S"
         ,Grammar.Production.mk_or
             (Grammar.Production.mk_nonterminal (Id.create "S"))
             (Grammar.Production.mk_terminal "s"))]
    ]
    (Grammar.rewrites
       (from_kvp_list_exn
          [(Id.create "S"
           ,Grammar.Production.mk_or
               (Grammar.Production.mk_nonterminal (Id.create "S"))
               (Grammar.Production.mk_terminal "s"))]))

let check_rewrites_easy_recursion_or_right _ =
  assert_grammar_list_unordered_equal
    [from_kvp_list_exn
       [(Id.create "S"
        ,Grammar.Production.mk_or
            (Grammar.Production.mk_terminal "s")
            (Grammar.Production.mk_or
               (Grammar.Production.mk_terminal "s")
               (Grammar.Production.mk_nonterminal (Id.create "S"))))]
    ;Grammar.from_kvp_list_exn
        (Grammar.Production.mk_or
           (Grammar.Production.mk_terminal "s")
           (Grammar.Production.mk_nonterminal (Id.create "S")))
        [(Id.create "S"
         ,Grammar.Production.mk_or
             (Grammar.Production.mk_terminal "s")
             (Grammar.Production.mk_nonterminal (Id.create "S")))]
    ]
    (Grammar.rewrites
       (from_kvp_list_exn
          [(Id.create "S"
           ,Grammar.Production.mk_or
               (Grammar.Production.mk_terminal "s")
               (Grammar.Production.mk_nonterminal (Id.create "S")))]))

let check_rewrites_doublerec _ =
  assert_grammar_list_unordered_equal
    [from_kvp_list_exn
       [(Id.create "S",
         Grammar.Production.mk_concat
           (Grammar.Production.mk_nonterminal (Id.create "T"))
           (Grammar.Production.mk_concat
              (Grammar.Production.mk_nonterminal (Id.create "T"))
              (Grammar.Production.mk_nonterminal (Id.create "S"))))
       ;(Id.create "T",
         Grammar.Production.mk_or
           (Grammar.Production.mk_nonterminal (Id.create "T"))
           (Grammar.Production.mk_nonterminal (Id.create "S")))]
    ;from_kvp_list_exn
        [(Id.create "S",
          Grammar.Production.mk_concat
            (Grammar.Production.mk_nonterminal (Id.create "T"))
            (Grammar.Production.mk_nonterminal (Id.create "S")))
        ;(Id.create "T",
          Grammar.Production.mk_or
            (Grammar.Production.mk_nonterminal (Id.create "T"))
            (Grammar.Production.mk_concat
               (Grammar.Production.mk_nonterminal (Id.create "T"))
               (Grammar.Production.mk_nonterminal (Id.create "S"))))]
    ;from_kvp_list_exn
        [(Id.create "S",
          Grammar.Production.mk_concat
            (Grammar.Production.mk_or
               (Grammar.Production.mk_nonterminal (Id.create "T"))
               (Grammar.Production.mk_nonterminal (Id.create "S")))
            (Grammar.Production.mk_nonterminal (Id.create "S")))
        ;(Id.create "T",
          Grammar.Production.mk_or
            (Grammar.Production.mk_nonterminal (Id.create "T"))
            (Grammar.Production.mk_nonterminal (Id.create "S")))]
    ;from_kvp_list_exn
        [(Id.create "S",
          Grammar.Production.mk_concat
            (Grammar.Production.mk_nonterminal (Id.create "T"))
            (Grammar.Production.mk_nonterminal (Id.create "S")))
        ;(Id.create "T",
          Grammar.Production.mk_or
            (Grammar.Production.mk_or
               (Grammar.Production.mk_nonterminal (Id.create "T"))
               (Grammar.Production.mk_nonterminal (Id.create "S")))
            (Grammar.Production.mk_nonterminal (Id.create "S")))]
    ;Grammar.from_kvp_list_exn
        (Grammar.Production.mk_concat
           (Grammar.Production.mk_nonterminal (Id.create "T"))
           (Grammar.Production.mk_nonterminal (Id.create "S")))
        [(Id.create "S",
          Grammar.Production.mk_concat
            (Grammar.Production.mk_nonterminal (Id.create "T"))
            (Grammar.Production.mk_nonterminal (Id.create "S")))
        ;(Id.create "T",
          Grammar.Production.mk_or
            (Grammar.Production.mk_nonterminal (Id.create "T"))
            (Grammar.Production.mk_nonterminal (Id.create "S")))]]
    (Grammar.rewrites
       (from_kvp_list_exn
          [(Id.create "S",
            Grammar.Production.mk_concat
              (Grammar.Production.mk_nonterminal (Id.create "T"))
              (Grammar.Production.mk_nonterminal (Id.create "S")))
          ;(Id.create "T",
            Grammar.Production.mk_or
              (Grammar.Production.mk_nonterminal (Id.create "T"))
              (Grammar.Production.mk_nonterminal (Id.create "S")))]))

let rewrites_suite =
  "rewrites Unit Tests" >:::
  ["check_rewrites_easy_recursion_concat_left" >:: check_rewrites_easy_recursion_concat_left
  ;"check_rewrites_easy_recursion_concat_right" >:: check_rewrites_easy_recursion_concat_right
  ;"check_rewrites_easy_recursion_or_left" >:: check_rewrites_easy_recursion_or_left
  ;"check_rewrites_easy_recursion_or_right" >:: check_rewrites_easy_recursion_or_right
  ;"check_rewrites_doublerec" >:: check_rewrites_doublerec
  ]

let _ = run_test_tt_main rewrites_suite
