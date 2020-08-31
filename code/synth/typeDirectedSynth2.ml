open MyStdLib
open Lang

module Production = ProbabilisticGrammar.Production

let rec synth_options
    (g1:ProbabilisticGrammar.t)
    (g2:ProbabilisticGrammar.t)
    (l:GrammarLinker.t)
    (ctx:Context.t)
    (destructed:bool)
    (next_var:int)
    (p:Production.t)
    (targets:ParseTree.t list)
    (size:int)
  : Converter.t list =
  let synth_options = synth_options g1 g2 l in
  let create_destruct
      ((i,p',ctx):Id.t * Production.t * Context.t)
    : Converter.t list =
    begin match p'.t_node with
      | Concat (p1,p2) ->
        let left_v = Id.from_int next_var in
        let right_v = Id.from_int (next_var+1) in
        let ctx =
          Context.insert_string_unsafe
            (Context.insert_string_unsafe ctx left_v p1)
            right_v
            p2
        in
        let cs =
          synth_options
            ctx
            true
            (next_var + 2)
            p
            targets
            (size - 4)
        in
        List.map
          ~f:(Converter.mk_concat_elim i left_v right_v)
          cs
      | Or (p1,p2,_) ->
        let next_v = Id.from_int next_var in
        let partitions = pair_partition (size-3) in
        List.concat_map
          ~f:(fun (left_size,right_size) ->
              let recurse p' size =
                let ctx_o =
                  Context.insert_string
                    ctx
                    next_v
                    p'
                in
                begin match ctx_o with
                  | None -> if size = 1 then [Converter.empty_func] else []
                  | Some ctx ->
                    synth_options
                      ctx
                      true
                      (next_var + 1)
                      p
                      targets
                      size
                end
              in
              let lefts = recurse p1 left_size in
              let rights = recurse p2 right_size in
              cartesian_map
                ~f:(Converter.mk_or_elim i next_v)
                lefts
                rights)
          partitions
      | Terminal _ -> failwith "something went wrong"
      | Nonterminal _ -> failwith "something went wrong"
      | Empty -> failwith "something went wrong"
    end
  in
  if size <= 0 then [] else
    begin match Production.destruct_nonterminal p with
      | Some i -> synth_options ctx destructed next_var (ProbabilisticGrammar.get_productions g2 i) targets size
      | None ->
        let use_context () : Converter.t list =
          if size = 1 then
            List.map
              ~f:(Converter.mk_variable)
              (Context.extract_matching_vars ctx l p)
          else if size = 2 && destructed then
            List.map
              ~f:(uncurry Converter.mk_apply)
              (Context.extract_matching_applications ctx l p)
          else
            []
        in
        let intro_recursion () : Converter.t list =
          let ps = Context.novel_recursion_string_elements l ctx in
          List.concat_map
            ~f:(fun (i,pl) ->
                let fid = Id.from_int next_var in
                let ctx = Context.empty_out ctx in
                let ctx = Context.insert_string_unsafe ctx i pl in
                let ctx =
                  Context.insert_func
                    ctx
                    fid
                    pl
                    p
                in
                let subsolns =
                  synth_options
                    ctx
                    false
                    (next_var+1)
                    p
                    targets
                    (size-3)
                in
                let subsolns =
                  List.filter
                    ~f:(Converter.is_applied fid)
                    subsolns
                in
                List.map
                  ~f:(Converter.mk_fix fid i)
                  subsolns)
            ps
        in
        let intro_form () : Converter.t list =
          begin match p.t_node with
            | Terminal s -> if size = 1 then [Converter.mk_string_intro s] else []
            | Concat (p1,p2) ->
              let partitions =
                pair_partition
                  (size-1)
              in
              List.concat_map
                ~f:(fun (s1,s2) ->
                    let left_converters =
                      synth_options
                        ctx
                        destructed
                        next_var
                        p1
                        targets
                        s1
                    in
                    let right_converters =
                      synth_options
                        ctx
                        destructed
                        next_var
                        p2
                        targets
                        s2
                    in
                    cartesian_map
                      ~f:(fun lc rc ->
                          Converter.mk_concat_intro
                            lc
                            rc)
                      left_converters
                      right_converters)
                partitions
            | Or (p1,p2,_) ->
              let left_converters =
                List.map
                  ~f:(Converter.mk_or_intro true)
                  (synth_options
                     ctx
                     destructed
                     next_var
                     p1
                     targets
                     (size-2))
              in
              let right_converters =
                List.map
                  ~f:(Converter.mk_or_intro false)
                  (synth_options
                     ctx
                     destructed
                     next_var
                     p2
                     targets
                     (size-2))
              in
              left_converters@right_converters
            | Nonterminal _ -> failwith "something went wrong"
            | Empty -> failwith "no function"
          end
        in
        let elim_form () : Converter.t list =
          let ps = Context.peels ctx in
          List.concat_map
            ~f:create_destruct
            ps
        in
        let anses =
          begin match p.t_node with
            | Or _ ->
              begin match Context.destruct_required ctx l p with
                | None ->
                  use_context () @ intro_form () @ elim_form () @ intro_recursion ()
                | Some ipc ->
                  print_endline "begin";
                  print_endline (Id.show (fst3 ipc));
                  print_endline (Production.show (snd3 ipc));
                  print_endline "end";
                  print_endline "";
                  create_destruct ipc
              end
            | _ ->
              use_context () @ intro_form ()
          end
        in
        List.iter
          ~f:(fun a -> if (Converter.size a <> size) then failwith ((Converter.show a) ^ " " ^ (string_of_int (Converter.size a)) ^ " " ^ (string_of_int size)))
          anses;
        anses
    end

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
  let a2 =
    Automata.from_grammar
      g2
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
    ProbabilisticGrammarBuilder.build
      g2
      s2s
  in
  let sizes = range 0 38 in
  let context_o = Context.insert_string (Context.empty pg1 pg2) (Id.from_int 0) (ProbabilisticGrammar.get_initial_production pg1) in
  let linker = GrammarLinker.create pg1 pg2 in
  let options =
    begin match context_o with
      | None -> [Converter.empty_func]
      | Some ctx ->
        List.concat_map
          ~f:(fun size ->
              synth_options
                pg1
                pg2
                linker
                ctx
                true
                1
                (ProbabilisticGrammar.get_initial_production pg2)
                output_parse_trees
                size)
          sizes
    end
  in
  let options =
    List.filter
      ~f:(fun c ->
          if Converter.nested_fix c then print_endline ((Converter.show c) ^ " " ^ (string_of_int (Converter.size c)));
          SymbolicEval.covers_all_examples c output_parse_trees)
      options
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
  let ans =
    Option.value_exn
      (List.min_elt
         ~compare:(fun (_,f1) (_,f2) -> Float.compare f1 f2)
         options_ranks)
  in
  fst ans
