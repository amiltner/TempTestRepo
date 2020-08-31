open MyStdLib
open Lang

module POConverterFloat =
struct
  include PairOf(Converter)(FloatModule)
  let po
      (_,f1)
      (_,f2)
    : int option =
    Some (Int.neg (Float.compare f1 f2))
end

module MaxForest = MaxForestOf(POConverterFloat)

let rec simplest_synth
    (g1:ProbabilisticGrammar.t)
    (g2:ProbabilisticGrammar.t)
    (l:GrammarLinker.t)
    (ctx:Context.t)
    (destructed:bool)
    (next_var:int)
    (p:ProbabilisticGrammar.Production.t)
    (targets:ParseTree.t list)
    (incoming_probability:Float.t)
    (outgoing_probability:Float.t)
  : MaxForest.t =
  let simplest_synth = simplest_synth g1 g2 l in
  let constructors =
    begin match p.t_node with
      | Nonterminal n ->
        let p = ProbabilisticGrammar.get_productions g2 n in
        simplest_synth
          ctx
          destructed
          next_var
          p
          targets
          incoming_probability
          outgoing_probability
      | Terminal s ->
        MaxForest.singleton
          (Converter.mk_string_intro s,
           Probability.single_kl_divergence incoming_probability outgoing_probability)
      | Concat (p1,p2) ->
        let mf1 =
          simplest_synth
            ctx
            destructed
            next_var
            p1
            targets
            incoming_probability
            outgoing_probability
        in
        let mf2 =
          simplest_synth
            ctx
            destructed
            next_var
            p2
            targets
            incoming_probability
            outgoing_probability
        in
        MaxForest.cartesian_map
          ~f:(fun (c1,f1) (c2,f2) ->
              (Converter.mk_concat_intro
                 c1
                 c2
              ,f1 +. f2))
          mf1
          mf2
      | Or (p1,p2,left_probability) ->
        let mf1 =
          MaxForest.map
            ~f:(fun (c,f) -> (Converter.mk_or_intro true c,f))
            (simplest_synth
               ctx
               destructed
               next_var
               p1
               targets
               incoming_probability
               (outgoing_probability*.left_probability))
        in
        let mf2 =
          MaxForest.map
            ~f:(fun (c,f) -> (Converter.mk_or_intro true c,f))
            (simplest_synth
               ctx
               destructed
               next_var
               p1
               targets
               incoming_probability
               (outgoing_probability*.(Probability.not left_probability)))
        in
        MaxForest.merge
          mf1
          mf2
      | Empty -> failwith "shouldnt happen"
    end
  in
  MaxForest.multi_merge [constructors]

let rec single_rewrite
    (g1:ProbabilisticGrammar.t)
    (g2:ProbabilisticGrammar.t)
    (l:GrammarLinker.t)
    (ctx:Context.t)
    (destructed:bool)
    (next_var:int)
    (p:ProbabilisticGrammar.Production.t)
    (targets:ParseTree.t list)
    (c:Converter.t)
    (incoming_probability:Float.t)
    (outgoing_probability:Float.t)
  : Converter.t list =
  let single_rewrite = single_rewrite g1 g2 l in
  begin match c with
    | EmptyFunc -> []
    | StringIntro s -> []
    | OrElim (i1,i2,c1,c2) ->
      let left_rewrites =
        single_rewrite
          ctx
          destructed
          next_var
          p
          targets
          c1
          incoming_probability
          outgoing_probability
      in
      let right_rewrites =
        single_rewrite
          ctx
          destructed
          next_var
          p
          targets
          c2
          incoming_probability
          outgoing_probability
      in
      let left_fulls =
        List.map
          ~f:(fun lr -> Converter.mk_or_elim i1 i2 lr c2)
          left_rewrites
      in
      let right_fulls =
        List.map
          ~f:(fun rr -> Converter.mk_or_elim i1 i2 c1 rr)
          right_rewrites
      in
      left_fulls@right_fulls
    | ConcatElim (i1,i2,i3,c) ->
      failwith "ah"
    | OrIntro (b,i) ->
      failwith "ah"
    | ConcatIntro (c1,c2) ->
      failwith "ah"
    | Variable i ->
      failwith "ah"
    | Apply (i1,i2) ->
      failwith "ah"
    | Fix (i1,i2,c) ->
      failwith "ah"
  end

let rec rewrite_synth
    (g1:ProbabilisticGrammar.t)
    (g2:ProbabilisticGrammar.t)
    (l:GrammarLinker.t)
    (ctx:Context.t)
    (destructed:bool)
    (next_var:int)
    (p:ProbabilisticGrammar.Production.t)
    (targets:ParseTree.t list)
  =
  let rewrite_synth = rewrite_synth g1 g2 l in
  begin match ProbabilisticGrammar.Production.destruct_nonterminal p with
    | Some i ->
      rewrite_synth
        ctx
        destructed
        next_var
        (ProbabilisticGrammar.get_productions g2 i)
        targets
    | None ->
      begin match p.t_node with
        | Concat (p1,p2) ->
          let c1 =
            rewrite_synth
              ctx
              destructed
              next_var
              p1
              targets
          in
          let c2 =
            rewrite_synth
              ctx
              destructed
              next_var
              p2
              targets
          in
          Converter.mk_concat_intro
            c1
            c2
        | Or (p1,p2,f) ->
          failwith "ah"
        | Empty ->
          failwith "ah"
        | Nonterminal _ ->
          failwith "ah"
        | Terminal _ ->
          failwith "ah"
      end
  end


let synth
    (g1:Grammar.t)
    (g2:Grammar.t)
    (s1s:string list)
    (s2s:string list)
  : Converter.t =
  let a1 =
    Automata.from_grammar
      g1
  in
  let a2 =
    Automata.from_grammar
      g2
  in
  let input_parses =
    List.map
      ~f:(Automata.parse_exn a1)
      s1s
  in
  let _ =
    List.map
      ~f:(ParseTree.from_bool_list g1)
      input_parses
  in
  let output_parses =
    List.map
      ~f:(Automata.parse_exn a2)
      s2s
  in
  let output_parse_trees =
    List.map
      ~f:(ParseTree.from_bool_list g2)
      output_parses
  in
  let pg1 =
    ProbabilisticGrammarBuilder.build_from_parses
      g1
      input_parses
  in
  let pg2 =
    ProbabilisticGrammarBuilder.build_from_parses
      g2
      output_parses
  in
  let context_o = Context.insert_string (Context.empty pg1 pg2) (Id.from_int 0) (ProbabilisticGrammar.get_initial_production pg1) in
  let linker = GrammarLinker.create pg1 pg2 in
  begin match context_o with
    | None -> Converter.empty_func
    | Some ctx ->
      rewrite_synth
        pg1
        pg2
        linker
        ctx
        true
        1
        (ProbabilisticGrammar.get_initial_production pg2)
        output_parse_trees
  end
