open MyStdLib
open Synth_asserts
open Lang
open Synth
open OUnitPlusPlus

(* begin apply *)
let from_kvp_list_exn = Grammar.from_kvp_list_exn (Grammar.Production.mk_nonterminal (Id.create "S"))
let test_apply_empty _ =
  assert_raises
    (Error.to_exn (Error.of_string "Option.value_exn None"))
    (fun () ->
       Eval.apply
         (from_kvp_list_exn [(Id.create "S",Grammar.Production.empty)])
         "s"
         Converter.empty_func)

let test_apply_bad_string _ =
  assert_raises
    (Error.to_exn (Error.of_string "Option.value_exn None"))
    (fun () ->
       Eval.apply
         (from_kvp_list_exn [(Id.create "S",Grammar.Production.mk_terminal "c")])
         "d"
         Converter.empty_func)

let test_apply_constant_constant _ =
  assert_string_equal
    "d"
    (Eval.apply
       (from_kvp_list_exn [(Id.create "S",Grammar.Production.mk_terminal "c")])
       "c"
       (Converter.mk_string_intro "d"))

let test_apply_simple_concat _ =
  assert_string_equal
    "de"
    (Eval.apply
       (from_kvp_list_exn [(Id.create "S",Grammar.Production.mk_terminal "c")])
       "c"
       (Converter.mk_concat_intro
          (Converter.mk_string_intro "d")
          (Converter.mk_string_intro "e")))

let test_apply_simple_or_elim_left _ =
  assert_string_equal
    "e"
    (Eval.apply
       (from_kvp_list_exn
          [(Id.create "S",
            (Grammar.Production.mk_or
               (Grammar.Production.mk_terminal "c")
               (Grammar.Production.mk_terminal "d")))])
       "c"
       (Converter.mk_or_elim
          (Id.from_int 0)
          (Id.from_int 1)
          (Converter.mk_string_intro "e")
          (Converter.mk_string_intro "z")))

let test_apply_simple_or_elim_right _ =
  assert_string_equal
    "e"
    (Eval.apply
       (from_kvp_list_exn
          [(Id.create "S",
            (Grammar.Production.mk_or
               (Grammar.Production.mk_terminal "c")
               (Grammar.Production.mk_terminal "d")))])
       "d"
       (Converter.mk_or_elim
          (Id.from_int 0)
          (Id.from_int 1)
          (Converter.mk_string_intro "z")
          (Converter.mk_string_intro "e")))

let test_apply_simple_concat_elim _ =
  assert_string_equal
    "e"
    (Eval.apply
       (from_kvp_list_exn
          [(Id.create "S",
            (Grammar.Production.mk_concat
               (Grammar.Production.mk_terminal "c")
               (Grammar.Production.mk_terminal "d")))])
       "cd"
       (Converter.mk_string_intro "e"))

let test_apply_simple_or_intro_left _ =
  assert_string_equal
    "e"
    (Eval.apply
       (from_kvp_list_exn
          [(Id.create "S",
            (Grammar.Production.mk_terminal "c"))])
       "c"
       (Converter.mk_or_intro
          true
          (Converter.mk_string_intro "e")))

let test_apply_simple_or_intro_right _ =
  assert_string_equal
    "e"
    (Eval.apply
       (from_kvp_list_exn
          [(Id.create "S",
            (Grammar.Production.mk_terminal "c"))])
       "c"
       (Converter.mk_or_intro
          false
          (Converter.mk_string_intro "e")))

let test_apply_complex _ =
  assert_string_equal
    "z1z2"
    (Eval.apply
       (from_kvp_list_exn
          [(Id.create "S",
            (Grammar.Production.mk_concat
               (Grammar.Production.mk_or
                  (Grammar.Production.mk_terminal "a")
                  (Grammar.Production.mk_terminal "b"))
               (Grammar.Production.mk_or
                  (Grammar.Production.mk_terminal "c")
                  (Grammar.Production.mk_terminal "d"))))])
       "bc"
       (Converter.mk_concat_elim
          (Id.from_int 0)
          (Id.from_int 1)
          (Id.from_int 2)
          (Converter.mk_or_elim
             (Id.from_int 1)
             (Id.from_int 3)
             (Converter.mk_or_elim
                (Id.from_int 2)
                (Id.from_int 4)
                (Converter.mk_string_intro "x")
                (Converter.mk_string_intro "y"))
             (Converter.mk_or_elim
                (Id.from_int 2)
                (Id.from_int 4)
                (Converter.mk_concat_intro
                   (Converter.mk_or_intro
                      true
                      (Converter.mk_string_intro "z1"))
                   (Converter.mk_or_intro
                      false
                      (Converter.mk_string_intro "z2")))
                (Converter.mk_string_intro "q")))))

let apply_suite =
  "apply Unit Tests" >:::
  ["test_apply_empty" >:: test_apply_empty
  ;"test_apply_bad_string" >:: test_apply_bad_string
  ;"test_apply_constant_constant" >:: test_apply_constant_constant
  ;"test_apply_simple_concat" >:: test_apply_simple_concat
  ;"test_apply_simple_or_elim_left" >:: test_apply_simple_or_elim_left
  ;"test_apply_simple_or_elim_right" >:: test_apply_simple_or_elim_right
  ;"test_apply_simple_concat_elim" >:: test_apply_simple_concat_elim
  ;"test_apply_simple_or_intro_left" >:: test_apply_simple_or_intro_left
  ;"test_apply_simple_or_intro_right" >:: test_apply_simple_or_intro_right
  ;"test_apply_complex" >:: test_apply_complex
  ]

let _ = run_test_tt_main apply_suite
(* end apply *)

(* begin requires_destruct *)
let test_requires_destruct_doublerec _ =
  let g1 =
    from_kvp_list_exn
      [(Id.create "S",
        (Grammar.Production.mk_or
           (Grammar.Production.mk_terminal "")
           (Grammar.Production.mk_concat
              (Grammar.Production.mk_nonterminal (Id.create "T"))
              (Grammar.Production.mk_nonterminal (Id.create "S")))))
      ;(Id.create "T",
        (Grammar.Production.mk_or
           (Grammar.Production.mk_terminal "a")
           (Grammar.Production.mk_concat
              (Grammar.Production.mk_terminal "b")
              (Grammar.Production.mk_nonterminal (Id.create "T")))))]
  in
  let g2 =
    from_kvp_list_exn
      [(Id.create "S",
        (Grammar.Production.mk_or
           (Grammar.Production.mk_terminal "")
           (Grammar.Production.mk_concat
              (Grammar.Production.mk_nonterminal (Id.create "T"))
              (Grammar.Production.mk_nonterminal (Id.create "S")))))
      ;(Id.create "T",
        (Grammar.Production.mk_or
           (Grammar.Production.mk_terminal "c")
           (Grammar.Production.mk_concat
              (Grammar.Production.mk_terminal "d")
              (Grammar.Production.mk_nonterminal (Id.create "T")))))]
  in
  let pg1 =
    ProbabilisticGrammarBuilder.to_probabilistic_grammar
      g1
      (ProbabilisticGrammarBuilder.from_grammar_basic g1)
  in
  let pg2 =
    ProbabilisticGrammarBuilder.to_probabilistic_grammar
      g2
      (ProbabilisticGrammarBuilder.from_grammar_basic g2)
  in
  let c = Context.empty pg1 pg2 in
  let c =
    Context.insert_func
      c
      (Id.from_int 0)
      (ProbabilisticGrammar.get_productions pg1 (Id.create "S"))
      (ProbabilisticGrammar.get_productions pg2 (Id.create "S"))
  in
  let linker = GrammarLinker.create pg1 pg2 in
  assert_false
    (Context.requires_destruct
       c
       linker
       (ProbabilisticGrammar.get_productions pg1 (Id.create "T"))
       (ProbabilisticGrammar.get_productions pg2 (Id.create "T")))

let requires_destruct_suite =
  "requires_destruct Unit Tests" >:::
  ["test_requires_destruct_doublerec" >:: test_requires_destruct_doublerec
  ]

let _ = run_test_tt_main requires_destruct_suite
(* end requires_destruct *)

(* begin synthesize *)
let test_synthesize_empty _ =
  assert_converter_equal
    (Converter.empty_func)
    (Synthesizer.synthesize
       (from_kvp_list_exn
          [(Id.create "S",Grammar.Production.empty)])
       (from_kvp_list_exn
          [(Id.create "S",Grammar.Production.empty)])
       []
       [])

let test_synthesize_empty_left _ =
  assert_converter_equal
    (Converter.empty_func)
    (Synthesizer.synthesize
       (from_kvp_list_exn
          [(Id.create "S",Grammar.Production.empty)])
       (from_kvp_list_exn [(Id.create "S",Grammar.Production.Terminal "b")])
       []
       [])

let test_synthesize_string _ =
  assert_converter_equal
    (Converter.mk_string_intro "b")
    (Synthesizer.synthesize
       (from_kvp_list_exn [(Id.create "S",Grammar.Production.mk_terminal "a")])
       (from_kvp_list_exn [(Id.create "S",Grammar.Production.Terminal "b")])
       []
       [])

let test_synthesize_symbols _ =
  assert_converter_equal
    (Converter.mk_string_intro "b")
    (Synthesizer.synthesize
       (from_kvp_list_exn
          [(Id.create "S",
            Grammar.Production.mk_nonterminal (Id.create "T"))
          ;(Id.create "T",
            Grammar.Production.mk_terminal "b")])
       (from_kvp_list_exn
          [(Id.create "S",
            Grammar.Production.mk_nonterminal (Id.create "T"))
          ;(Id.create "T",
            Grammar.Production.mk_terminal "b")])
       []
       [])

let test_synthesize_or_left _ =
  assert_converter_equal
    (Converter.mk_string_intro "a")
    (Synthesizer.synthesize
       (from_kvp_list_exn
          [(Id.create "S",
            Grammar.Production.mk_or
              (Grammar.Production.mk_terminal "a")
              (Grammar.Production.mk_terminal "b"))])
       (from_kvp_list_exn
          [(Id.create "S",
            Grammar.Production.mk_terminal "a")])
       []
       [])

let test_synthesize_or_right _ =
  assert_converter_equal
    (Converter.mk_or_intro
       true
       (Converter.mk_string_intro "a"))
    (Synthesizer.synthesize
       (from_kvp_list_exn
          [(Id.create "S",
            Grammar.Production.mk_terminal "a")])
       (from_kvp_list_exn
          [(Id.create "S",
            Grammar.Production.mk_or
              (Grammar.Production.mk_terminal "a")
              (Grammar.Production.mk_terminal "b"))])
       []
       [])

let test_synthesize_distributed_concat_left _ =
  assert_converter_equal
    (Converter.mk_string_intro "a")
    (Synthesizer.synthesize
       (from_kvp_list_exn
          [(Id.create "S",
            Grammar.Production.mk_concat
              (Grammar.Production.mk_nonterminal (Id.create "T"))
              (Grammar.Production.mk_nonterminal (Id.create "T")))
          ;(Id.create "T",
            Grammar.Production.mk_or
              (Grammar.Production.mk_terminal "a")
              (Grammar.Production.mk_terminal "b"))])
       (from_kvp_list_exn
          [(Id.create "S",(Grammar.Production.mk_terminal "a"))])
       []
       [])

let test_synthesize_distributed_concat_right _ =
  assert_converter_equal
    (Converter.mk_concat_intro
       (Converter.mk_or_intro
          true
          (Converter.mk_string_intro "a"))
       (Converter.mk_or_intro
          true
          (Converter.mk_string_intro "a")))
    (Synthesizer.synthesize
       (from_kvp_list_exn
          [(Id.create "S",(Grammar.Production.mk_terminal "a"))])
       (from_kvp_list_exn
          [(Id.create "S",
            Grammar.Production.mk_concat
              (Grammar.Production.mk_nonterminal (Id.create "T"))
              (Grammar.Production.mk_nonterminal (Id.create "T")))
          ;(Id.create "T",
            Grammar.Production.mk_or
              (Grammar.Production.mk_terminal "a")
              (Grammar.Production.mk_terminal "b"))])
       []
       [])

let test_synthesize_disjunct_union _ =
  assert_converter_equal
    (Converter.mk_string_intro "a")
    (Synthesizer.synthesize
       (from_kvp_list_exn
          [(Id.create "S",
            (Grammar.Production.mk_or
               (Grammar.Production.mk_terminal "a")
               Grammar.Production.empty))])
       (from_kvp_list_exn
          [(Id.create "S",Grammar.Production.mk_terminal "a")])
       []
       [])

let test_synthesize_probabilistic_straight _ =
  assert_converter_equal
    (Converter.mk_variable (Id.from_int 0))
    (Synthesizer.synthesize
       (from_kvp_list_exn
          [(Id.create "S",
            (Grammar.Production.mk_or
               (Grammar.Production.mk_terminal "a")
               (Grammar.Production.mk_terminal "b")))])
       (from_kvp_list_exn
          [(Id.create "S",
            (Grammar.Production.mk_or
               (Grammar.Production.mk_terminal "a")
               (Grammar.Production.mk_terminal "b")))])
       ["a";"b"]
       ["a";"b"])

let test_synthesize_probabilistic_swap _ =
  assert_converter_equal
    (Converter.mk_or_elim
       (Id.from_int 0)
       (Id.from_int 1)
       (Converter.mk_or_intro false (Converter.mk_string_intro "b"))
       (Converter.mk_or_intro true (Converter.mk_string_intro "a")))
    (Synthesizer.synthesize
       (from_kvp_list_exn
          [(Id.create "S",
            (Grammar.Production.mk_or
               (Grammar.Production.mk_terminal "a")
               (Grammar.Production.mk_terminal "b")))])
       (from_kvp_list_exn
          [(Id.create "S",
            (Grammar.Production.mk_or
               (Grammar.Production.mk_terminal "a")
               (Grammar.Production.mk_terminal "b")))])
       ["a";"a";"b"]
       ["a";"b";"b"])

let test_synthesize_probabilistic_merge _ =
  assert_converter_equal
    (Converter.mk_or_intro true (Converter.mk_string_intro "a"))
    (Synthesizer.synthesize
       (from_kvp_list_exn
          [(Id.create "S",
            (Grammar.Production.mk_or
               (Grammar.Production.mk_terminal "a")
               (Grammar.Production.mk_terminal "b")))])
       (from_kvp_list_exn
          [(Id.create "S",
            (Grammar.Production.mk_or
               (Grammar.Production.mk_terminal "a")
               (Grammar.Production.mk_terminal "b")))])
       ["a";"a";"b";"b"]
       ["a";"a";"a"])

let test_synthesize_infinitary_ident _ =
  assert_converter_equal
    (Converter.mk_variable (Id.from_int 0))
    (Synthesizer.synthesize
       (from_kvp_list_exn
          [(Id.create "S",
            (Grammar.Production.mk_or
               (Grammar.Production.mk_terminal "")
               (Grammar.Production.mk_concat
                  (Grammar.Production.mk_terminal "a")
                  (Grammar.Production.mk_nonterminal (Id.create "S")))))])
       (from_kvp_list_exn
          [(Id.create "S",
            (Grammar.Production.mk_or
               (Grammar.Production.mk_terminal "")
               (Grammar.Production.mk_concat
                  (Grammar.Production.mk_terminal "a")
                  (Grammar.Production.mk_nonterminal (Id.create "S")))))])
       ["a";"a";"a";"a"]
       ["a";"a"])

let test_synthesize_simple_recursion _ =
  assert_converter_equal
    (Converter.mk_fix
       (Id.from_int 1)
       (Id.from_int 0)
       (Converter.mk_or_elim
          (Id.from_int 0)
          (Id.from_int 2)
          (Converter.mk_or_intro
             true
             (Converter.mk_string_intro ""))
             (Converter.mk_concat_elim
                (Id.from_int 2)
                (Id.from_int 3)
                (Id.from_int 4)
                (Converter.mk_or_intro
                   false
                   (Converter.mk_concat_intro
                      (Converter.mk_string_intro "b")
                      (Converter.mk_apply
                         (Id.from_int 1)
                         (Id.from_int 4)))))))
    (Synthesizer.synthesize
       (from_kvp_list_exn
          [(Id.create "S",
            (Grammar.Production.mk_or
               (Grammar.Production.mk_terminal "")
               (Grammar.Production.mk_concat
                  (Grammar.Production.mk_terminal "a")
                  (Grammar.Production.mk_nonterminal (Id.create "S")))))])
       (from_kvp_list_exn
          [(Id.create "S",
            (Grammar.Production.mk_or
               (Grammar.Production.mk_terminal "")
               (Grammar.Production.mk_concat
                  (Grammar.Production.mk_terminal "b")
                  (Grammar.Production.mk_nonterminal (Id.create "S")))))])
       ["a";"aa";"aaa";"aaaa";"aaaaa";"aaaaaa";"aaaaaaa";"aaaaaaaaaaaaaa"]
       ["b";"bb";"bbb";"bbbb";"bbbbb";"bbbbbb";"bbbbbbb";"bbbbbbbbbbbbbb"])

let test_synthesize_inner_recursion _ =
  assert_converter_equal
    (Converter.mk_fix
       (Id.from_int 1)
       (Id.from_int 0)
       (Converter.mk_or_elim
          (Id.from_int 0)
          (Id.from_int 2)
          (Converter.mk_or_intro
             true
             (Converter.mk_string_intro ""))
          (Converter.mk_concat_elim
             (Id.from_int 2)
             (Id.from_int 3)
             (Id.from_int 4)
             (Converter.mk_or_intro
                false
                (Converter.mk_concat_intro
                   (Converter.mk_fix
                      (Id.from_int 5)
                      (Id.from_int 3)
                      (Converter.mk_or_elim
                         (Id.from_int 3)
                         (Id.from_int 6)
                         (Converter.mk_or_intro
                            true
                            (Converter.mk_string_intro "c"))
                         (Converter.mk_concat_elim
                            (Id.from_int 6)
                            (Id.from_int 7)
                            (Id.from_int 8)
                            (Converter.mk_or_intro
                               false
                               (Converter.mk_concat_intro
                                  (Converter.mk_string_intro "d")
                                  (Converter.mk_apply
                                     (Id.from_int 5)
                                     (Id.from_int 8)))))))
                   (Converter.mk_apply
                      (Id.from_int 1)
                      (Id.from_int 4)))))))
    (Synthesizer.synthesize
       (from_kvp_list_exn
          [(Id.create "S",
            (Grammar.Production.mk_or
               (Grammar.Production.mk_terminal "")
               (Grammar.Production.mk_concat
                  (Grammar.Production.mk_nonterminal (Id.create "T"))
                  (Grammar.Production.mk_nonterminal (Id.create "S")))))
          ;(Id.create "T",
            (Grammar.Production.mk_or
               (Grammar.Production.mk_terminal "a")
               (Grammar.Production.mk_concat
                  (Grammar.Production.mk_terminal "b")
                  (Grammar.Production.mk_nonterminal (Id.create "T")))))])
       (from_kvp_list_exn
          [(Id.create "S",
            (Grammar.Production.mk_or
               (Grammar.Production.mk_terminal "")
               (Grammar.Production.mk_concat
                  (Grammar.Production.mk_nonterminal (Id.create "T"))
                  (Grammar.Production.mk_nonterminal (Id.create "S")))))
          ;(Id.create "T",
            (Grammar.Production.mk_or
               (Grammar.Production.mk_terminal "c")
               (Grammar.Production.mk_concat
                  (Grammar.Production.mk_terminal "d")
                  (Grammar.Production.mk_nonterminal (Id.create "T")))))])
       ["a";"aa";"aaa";"aaaa";"aaaaa";"aaaaaa";"aaaaaaa";"aaaaaaaaaaaaaa";"ba";"bbba"]
       ["c";"cc";"ccc";"cccc";"ccccc";"cccccc";"ccccccc";"cccccccccccccc";"dc";"dddc"])

(*let _ = (Synthesizer.synthesize
       (from_kvp_list_exn
          [(Id.create "S",
            (Grammar.Production.mk_or
               (Grammar.Production.mk_terminal "")
               (Grammar.Production.mk_concat
                  (Grammar.Production.mk_nonterminal (Id.create "T"))
                  (Grammar.Production.mk_nonterminal (Id.create "S")))))
          ;(Id.create "T",
            (Grammar.Production.mk_or
               (Grammar.Production.mk_terminal "a")
               (Grammar.Production.mk_concat
                  (Grammar.Production.mk_terminal "b")
                  (Grammar.Production.mk_nonterminal (Id.create "T")))))])
       (from_kvp_list_exn
          [(Id.create "S",
            (Grammar.Production.mk_or
               (Grammar.Production.mk_terminal "")
               (Grammar.Production.mk_concat
                  (Grammar.Production.mk_nonterminal (Id.create "T"))
                  (Grammar.Production.mk_nonterminal (Id.create "S")))))
          ;(Id.create "T",
            (Grammar.Production.mk_or
               (Grammar.Production.mk_terminal "c")
               (Grammar.Production.mk_concat
                  (Grammar.Production.mk_terminal "d")
                  (Grammar.Production.mk_nonterminal (Id.create "T")))))])
       ["a";"aa";"aaa";"aaaa";"aaaaa";"aaaaaa";"aaaaaaa";"aaaaaaaaaaaaaa";"ba";"bbba"]
       ["c";"cc";"ccc";"cccc";"ccccc";"cccccc";"ccccccc";"cccccccccccccc";"dc";"dddc"])*)

let type_equiv_suite =
  "RigidSynth Unit Tests" >:::
  ["test_synthesize_empty" >:: test_synthesize_empty
  ;"test_synthesize_empty_left" >:: test_synthesize_empty_left
  ;"test_synthesize_string" >:: test_synthesize_string
  ;"test_synthesize_symbols" >:: test_synthesize_symbols
  ;"test_synthesize_or_left" >:: test_synthesize_or_left
  ;"test_synthesize_or_right" >:: test_synthesize_or_right
  ;"test_synthesize_distributed_concat_left" >:: test_synthesize_distributed_concat_left
  ;"test_synthesize_distributed_concat_right" >:: test_synthesize_distributed_concat_right
  ;"test_synthesize_disjunct_union" >:: test_synthesize_disjunct_union
  ;"test_synthesize_probabilistic_straight" >:: test_synthesize_probabilistic_straight
  ;"test_synthesize_probabilistic_swap" >:: test_synthesize_probabilistic_swap
  ;"test_synthesize_probabilistic_merge" >:: test_synthesize_probabilistic_merge
  ;"test_synthesize_infinitary_ident" >:: test_synthesize_infinitary_ident
  ;"test_synthesize_simple_recursion" >:: test_synthesize_simple_recursion
  ;"test_synthesize_inner_recursion" >:: test_synthesize_inner_recursion
  ]

(*let _ = run_test_tt_main type_equiv_suite*)
(* end synthesize *)
