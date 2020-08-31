open MyStdLib

module Production = struct
  type t =
    {
      t_node : t_node ;
      original : Grammar.Production.t ;
    }
  and t_node =
    | Nonterminal of Id.t
    | Terminal of string
    | Concat of t * t
    | Or of t * t * (int ref) * (int ref)
    | Empty
  [@@deriving bin_io, eq, hash, ord, sexp, show]

  let fold
      (type a)
      ~(nonterminal_f:Id.t -> a)
      ~(terminal_f:string -> a)
      ~(concat_f:a -> a -> a)
      ~(or_f:a -> a -> int ref -> int ref -> a)
      ~(empty_f:a)
      (s:t)
    : a =
    let rec fold_internal
        (s:t)
      : a =
      begin match s.t_node with
        | Nonterminal i -> nonterminal_f i
        | Terminal s -> terminal_f s
        | Concat (s1,s2) -> concat_f (fold_internal s1) (fold_internal s2)
        | Or (s1,s2,left,total) -> or_f (fold_internal s1) (fold_internal s2) left total
        | Empty -> empty_f
      end
    in
    fold_internal s

  let rec from_grammar_production_basic
      (p:Grammar.Production.t)
    : t =
    let tn =
      begin match p with
        | Nonterminal nt -> Nonterminal(nt)
        | Terminal s -> Terminal s
        | Concat (p1,p2) ->
          Concat
            (from_grammar_production_basic p1
            ,from_grammar_production_basic p2)
        | Or (p1,p2) ->
          Or
            (from_grammar_production_basic p1
            ,from_grammar_production_basic p2
            ,ref 0
            ,ref 0)
        | Empty -> Empty
      end
    in
    { t_node = tn; original = p }

  let extract_grammar_production
      (p:t)
    : Grammar.Production.t =
    p.original

  module ProbabilisticProduction = ProbabilisticGrammar.Production
end

module ProdDict = DictOf(Id)(Production)

type t =
  {
    dict  : ProdDict.t ;
    start : Production.t       ;
    orig  : Grammar.t  ;
  }
[@@deriving eq, hash, ord, show]

let get_productions (d:t) (s:Id.t) : Production.t =
  begin match ProdDict.lookup d.dict s with
    | None -> failwith "bad production"
    | Some ps -> ps
  end

let get_initial_production (d:t) : Production.t =
  d.start

let add_production (d:t) (s:Id.t) (p:Production.t) =
  let dict =
    ProdDict.insert_or_combine
      ~combiner:(fun x y -> failwith "ahh")
      d.dict
      s
      p
  in
  { d with dict = dict }

let update_start (g:t) (start:Production.t) : t =
  { g with start = start }

let symbol_production_list (g:t) : Production.t * (Id.t * Production.t) list =
  let start = g.start in
  let list = ProdDict.as_kvp_list g.dict in
  (start,list)

let initialize
    (start:Production.t)
    (orig:Grammar.t)
  : t =
  {
    dict  = ProdDict.empty ;
    start = start          ;
    orig  = orig           ;
  }

let add_data
    (g:t)
    (cs:bool list)
  : unit =
  let rec add_data_production
      (p:Production.t)
      (cs:bool list)
    : bool list =
    begin match p.t_node with
      | Nonterminal i ->
        add_data_production
          (get_productions
             g
             i)
          cs
      | Terminal _ -> cs
      | Concat (p1,p2) ->
        let cs =
          add_data_production
            p1
            cs
        in
        add_data_production
          p2
          cs
      | Or (p1,p2,lr,tr) ->
        tr := !tr+1;
        let (left_taken,cs) = split_by_first_exn cs in
        if left_taken then
          (lr := !lr+1;
           add_data_production
             p1
             cs)
        else
          add_data_production
            p2
            cs
      | Empty -> cs
    end
  in
  let remainder =
    add_data_production
      (get_initial_production g)
      cs
  in
  assert (Int.equal (List.length remainder) 0)

let from_kvp_list_exn
    (g:Grammar.t)
    (start:Production.t)
    (rs:(Id.t * Production.t) list)
  : t =
  List.fold
    ~f:(fun g (i,ps) -> add_production g i ps)
    ~init:(initialize start g)
    rs

let from_grammar_basic
    (g:Grammar.t)
  : t =
  let (start,ids_prods) =
    Grammar.symbol_production_list
      g
  in
  let ids_prods =
    List.map
      ~f:(fun (i,p) -> (i,Production.from_grammar_production_basic p))
      ids_prods
  in
  let start = Production.from_grammar_production_basic start in
  from_kvp_list_exn g start ids_prods

let from_parse_data
    (g:Grammar.t)
    (parses:bool list list)
  : t =
  let builder =
    from_grammar_basic
      g
  in
  List.iter
    ~f:(add_data builder)
    parses;
  builder

let from_grammar_data
    (g:Grammar.t)
    (ss:string list)
  : t =
  let a = Automata.from_grammar g in
  let parses =
    List.map
      ~f:(fun s ->
          Option.value_exn
            (Automata.parse a s))
      ss
  in
  from_parse_data
    g
    parses

let rec build_probabilistic_production
    (g:Grammar.t)
    (p:Production.t)
  : ProbabilisticGrammar.Production.t =
  let t_node =
    begin match p.t_node with
      | Nonterminal n -> ProbabilisticGrammar.Production.Nonterminal n
      | Terminal s -> Terminal s
      | Concat (s1,s2) -> Concat (build_probabilistic_production g s1,build_probabilistic_production g s2)
      | Or (p1,p2,left_ref,total_ref) ->
        let p1 = build_probabilistic_production g p1 in
        let p2 = build_probabilistic_production g p2 in
        let total = !total_ref in
        let left = !left_ref in
        let probability =
          if Int.equal total 0 then
            if
              Automata.is_empty
                (Automata.from_grammar_production
                   g
                   (ProbabilisticGrammar.Production.extract_grammar_production p1)) then
              0.
            else if
              Automata.is_empty
                (Automata.from_grammar_production
                   g
                   (ProbabilisticGrammar.Production.extract_grammar_production p2)) then
              1.0
            else
              0.5
          else
            (Float.of_int left) /. (Float.of_int total)
        in
        Or (p1,p2,probability)
      | Empty -> Empty
    end
  in
  {
    t_node = t_node ;
    original = p.original ;
  }

let to_probabilistic_grammar
    (g:Grammar.t)
    (builder:t)
  : ProbabilisticGrammar.t =
  let (start,ids_prods) =
    symbol_production_list
      builder
  in
  let ids_prods =
    List.map
      ~f:(fun (i,p) -> (i,build_probabilistic_production g p))
      ids_prods
  in
  let start = build_probabilistic_production g start in
  ProbabilisticGrammar.from_kvp_list_exn g start ids_prods

let build
    (g:Grammar.t)
    (ss:string list)
  : ProbabilisticGrammar.t =
  let builder =
    from_grammar_data
      g
      ss
  in
  to_probabilistic_grammar
    g
    builder

let build_from_parses
    (g:Grammar.t)
    (parses:bool list list)
  : ProbabilisticGrammar.t =
  let builder =
    from_parse_data
      g
      parses
  in
  to_probabilistic_grammar
    g
    builder
