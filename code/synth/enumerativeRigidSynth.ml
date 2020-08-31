open MyStdLib
open Lang

module Production = ProbabilisticGrammar.Production

let synth_options
    (g1:ProbabilisticGrammar.t)
    (g2:ProbabilisticGrammar.t)
  : Converter.t list =
  let rec synth_constructors
      (available_terminals:int)
      (p:Production.t)
    : Converter.t list =
    if available_terminals = 0 then
      [Converter.empty_func]
    else
      begin match p.t_node with
        | Nonterminal i ->
          synth_constructors
            available_terminals
            (ProbabilisticGrammar.get_productions g2 i)
        | Terminal s ->
          [Converter.mk_string_intro s]
        | Concat (s1,s2) ->
          let t1s =
            synth_constructors
              available_terminals
              s1
          in
          let t2s =
            synth_constructors
              available_terminals
              s2
          in
          cartesian_map
            ~f:(fun t1 t2 -> Converter.mk_concat_intro t1 t2)
            t1s
            t2s
        | Or (s1,s2,_) ->
          let t1s =
            synth_constructors
              available_terminals
              s1
          in
          let t2s =
            synth_constructors
              available_terminals
              s2
          in
          (List.map ~f:(Converter.mk_or_intro true) t1s)
          @ (List.map ~f:(Converter.mk_or_intro false) t2s)
        | Empty -> []
      end
  in
  let rec synth_destructors
      (ps:(Id.t * Production.t) list)
      (next_var:int)
    : Converter.t list =
    begin match ps with
      | [] ->
        synth_constructors
          next_var
          (ProbabilisticGrammar.get_initial_production g2)
      | (i,p1)::ps ->
        if not (ProbabilisticGrammar.is_nonempty_production g1 p1) then
          [Converter.empty_func]
        else
          begin match p1.t_node with
            | Nonterminal s ->
              synth_destructors
                ((i,ProbabilisticGrammar.get_productions g1 s)::ps)
                next_var
            | Or (p11,p12,_) ->
              let cur_var = Id.from_int next_var in
              let p11_transforms =
                synth_destructors
                  ((cur_var,p11)::ps)
                  (next_var+1)
              in
              let p12_transforms =
                synth_destructors
                  ((cur_var,p12)::ps)
                  (next_var+1)
              in
              cartesian_map
                ~f:(Converter.mk_or_elim i cur_var)
                p11_transforms
                p12_transforms
            | Concat (p1,p2) ->
              let p1_var = Id.from_int next_var in
              let p2_var = Id.from_int (next_var+1) in
              List.map
                ~f:(Converter.mk_concat_elim i p1_var p2_var)
                (synth_destructors
                   ((p1_var,p1)::(p2_var,p2)::ps)
                   (next_var+2))
            | Terminal s ->
              synth_destructors
                ps
                next_var
            | Empty ->
              failwith "shouldn't happen"
          end
    end
  in
  synth_destructors
    [(Id.from_int 0,ProbabilisticGrammar.get_initial_production g1)]
    1

let calculate_generated_probability
    (desired_pg:ProbabilisticGrammar.t)
    (input_g:Grammar.t)
    (output_g:Grammar.t)
    (parse_trees:ParseTree.t list)
    (c:Converter.t)
  : Float.t option =
  let new_parses =
    List.map
      ~f:(fun parse ->
          ParseTree.to_bool_list
            (Eval.parse_tree_apply
               parse
               c))
      parse_trees
  in
  let new_pg =
    ProbabilisticGrammarBuilder.build_from_parses
      output_g
      new_parses
  in
  ProbabilisticGrammar.kl_divergence
    desired_pg
    new_pg

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
  let input_parses =
    List.map
      ~f:(Automata.parse_exn a1)
      s1s
  in
  let input_parse_trees =
    List.map
      ~f:(ParseTree.from_bool_list g1)
      input_parses
  in
  let pg1 =
    ProbabilisticGrammarBuilder.build_from_parses
      g1
      input_parses
  in
  let pg2 =
    ProbabilisticGrammarBuilder.build
      g2
      s2s
  in
  let options =
    synth_options
      pg1
      pg2
  in
  let options_ranks =
    List.filter_map
      ~f:(fun o ->
          let p_o = calculate_generated_probability pg2 g1 g2 input_parse_trees o in
          begin match p_o with
            | None -> None
            | Some p -> Some (o,p)
          end)
      options
  in
  fst
    (Option.value_exn
       (List.min_elt
          ~compare:(fun (_,f1) (_,f2) -> Float.compare f1 f2)
          options_ranks))
