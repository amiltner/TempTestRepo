open MyStdLib
open Lang

module Production = ProbabilisticGrammar.Production

type t =
  {
    string_dict  : (Id.t * Production.t) list ;
    func_dict    : (Id.t * Production.t * Production.t) list ;
    left_grammar : ProbabilisticGrammar.t ;
    right_grammar : ProbabilisticGrammar.t ;
  }
[@@deriving eq, hash, ord, show]

let insert_string_unsafe
    (c:t)
    (i:Id.t)
    (p:Production.t)
  : t =
  let rec insert
      (p:Production.t)
    : t =
    begin match p.t_node with
      | Nonterminal nt -> insert (ProbabilisticGrammar.get_productions c.left_grammar nt)
      | Terminal _ ->
        c
      | _ ->
        { c with
          string_dict = (i,p)::c.string_dict }
    end
  in
  insert p

let insert_string
    (c:t)
    (i:Id.t)
    (p:Production.t)
  : t option =
  if ProbabilisticGrammar.is_nonempty_production c.left_grammar p then
    Some (insert_string_unsafe c i p)
  else
    None

let insert_func
    (c:t)
    (i:Id.t)
    (pl:Production.t)
    (pr:Production.t)
  : t =
  let pl = ProbabilisticGrammar.materialize c.left_grammar pl in
  let pr = ProbabilisticGrammar.materialize c.right_grammar pr in
  {
    c with func_dict = (i,pl,pr)::c.func_dict
  }

let peels
    (c:t)
  : (Id.t * Production.t * t) list =
  List.map
    ~f:(fun ((i,p),ps) ->
        let c = { c with string_dict = ps } in
        (i,p,c))
    (all_peels (c.string_dict))

let remove
    (c:t)
    (i:Id.t)
  : t =
  let string_dict =
    List.filter
      ~f:(not % (Id.equal i) % fst)
      c.string_dict
  in
  { c with string_dict = string_dict }

let string_elements
    (c:t)
  : (Id.t * Production.t) list =
  c.string_dict

let novel_recursion_string_elements
    (l:GrammarLinker.t)
    (c:t)
  : (Id.t * Production.t) list =
  let existing_recursion =
    List.map
      ~f:snd3
      c.func_dict
  in
  List.filter
    ~f:(fun (i,p) ->
        Grammar.is_recursive_production_modulo
          l.left_grammar
          (List.map ~f:Production.extract_grammar_production existing_recursion)
          (Production.extract_grammar_production p))
  c.string_dict

let empty
    (g1:ProbabilisticGrammar.t)
    (g2:ProbabilisticGrammar.t)
  : t =
  {
    string_dict  = [];
    func_dict    = [];
    left_grammar = g1 ;
    right_grammar = g2 ;
  }

let empty_out
    (c:t)
  : t =
  {
    c with string_dict = []; func_dict = [];
  }

let extract_matching_vars
    (c:t)
    (l:GrammarLinker.t)
    (p:Production.t)
  : Id.t list =
  List.filter_map
    ~f:(fun (i,pl) ->
        if GrammarLinker.definitionally_equivalent_lr l pl.original p.original then
          Some i
        else
          None)
    c.string_dict

let extract_matching_funcs
    (c:t)
    (l:GrammarLinker.t)
    (p:Production.t)
  : (Id.t * Production.t) list =
  List.filter_map
    ~f:(fun (i,pl,pr) ->
        if GrammarLinker.definitionally_equivalent_rr l pr.original p.original then
          Some (i,pl)
        else
          None)
    c.func_dict

let requires_destruct
    (c:t)
    (l:GrammarLinker.t)
    (pl:Production.t)
    (pr:Production.t)
  : bool =
  begin match Production.destruct_concat pl with
    | Some _ -> true
    | None ->
      let all_subprods =
        ProbabilisticGrammar.get_all_subproductions
          l.right_pgrammar
          pr
      in
      let cannot_ident_subprod subprod =
        not (GrammarLinker.definitionally_equivalent_lr
               l
               (ProbabilisticGrammar.Production.extract_grammar_production pl)
               (ProbabilisticGrammar.Production.extract_grammar_production subprod))
      in
      let cannot_applyto_subprod subprod =
        let valid_funcs = extract_matching_funcs c l subprod in
        List.for_all
          ~f:(fun (_,fd) ->
              not
                (GrammarLinker.definitionally_equivalent_ll
                   l
                   (ProbabilisticGrammar.Production.extract_grammar_production pl)
                   (ProbabilisticGrammar.Production.extract_grammar_production fd)))
          valid_funcs
      in
      let existing_recursion =
        List.map
          ~f:snd3
          c.func_dict
      in
      (List.for_all ~f:cannot_ident_subprod all_subprods)
      && (List.for_all ~f:cannot_applyto_subprod all_subprods)
      && (not (Grammar.is_recursive_production_modulo
                 (l.left_grammar)
                 (List.map ~f:Production.extract_grammar_production existing_recursion)
                 (Production.extract_grammar_production pl)))
  end

let extract_matching_vars_leftonly
    (c:t)
    (l:GrammarLinker.t)
    (p:Production.t)
  : Id.t list =
  List.filter_map
    ~f:(fun (i,pl) ->
        if GrammarLinker.definitionally_equivalent_ll l pl.original p.original then
          Some i
        else
          None)
    c.string_dict

let extract_matching_applications
    (c:t)
    (l:GrammarLinker.t)
    (p:Production.t)
  : (Id.t * Id.t) list =
  let valid_funcs =
    extract_matching_funcs
      c
      l
      p
  in
  List.concat_map
    ~f:(fun (fi,fd) ->
        let valid_inputs = extract_matching_vars_leftonly c l fd in
        List.map
          ~f:(fun vi -> (fi,vi))
          valid_inputs)
    valid_funcs

let destruct_required
    (c:t)
    (l:GrammarLinker.t)
    (pr:Production.t)
  : (Id.t * Production.t * t) option =
  let rec make_destruct
      (vs:(Id.t * Production.t) list)
      (processed_vs:(Id.t * Production.t) list)
    : (Id.t * Production.t * t) option =
    begin match vs with
      | [] -> None
      | (vi,vp)::t ->
        if requires_destruct c l vp pr then
          let c =
            { c with
              string_dict = (processed_vs@t)
            }
          in
          Some (vi,vp,c)
        else
          make_destruct t ((vi,vp)::processed_vs)
    end
  in
  (*let infinite_destruct
      (p:Production.t)
    : bool =
    if Grammar.is_recursive_production_modulo
        l.left_grammar
        []
        (Production.extract_grammar_production p) then
      let all_subprods =
        ProbabilisticGrammar.get_all_subproductions
          l.left_pgrammar
          p
      in
      List.for_all
      false
    else
      false
    in*)
  make_destruct c.string_dict []

let rec extract_simple_lefts
    (c:t)
    (l:GrammarLinker.t)
    (p:Production.t)
  : Converter.t list =
  begin match p.t_node with
    | Nonterminal nt ->
      let p = ProbabilisticGrammar.get_productions l.left_pgrammar nt in
      extract_simple_lefts
        c
        l
        p
    | _ ->
      let var_inputs =
        List.map
          ~f:Converter.mk_variable
          (extract_matching_vars c l p)
      in
      let sub_inputs =
        begin match p.t_node with
          | Concat (p1,p2) ->
            let inputs1 = extract_simple_lefts c l p1 in
            let inputs2 = extract_simple_lefts c l p2 in
            cartesian_map
              ~f:Converter.mk_concat_intro
              inputs1
              inputs2
          | Terminal s -> [Converter.mk_string_intro s]
          | _ -> []
        end
      in
      var_inputs@sub_inputs
  end
