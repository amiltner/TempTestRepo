open MyStdLib
open Lang

module Production = Grammar.Production
module ProductionPairBoolDict = DictOf(PairOf(Production)(Production))(BoolModule)

type t =
  {
    left_pgrammar : ProbabilisticGrammar.t ;
    right_pgrammar : ProbabilisticGrammar.t ;
    left_grammar : Grammar.t ;
    right_grammar : Grammar.t ;
    mutable equivalent_pairs_ll : ProductionPairBoolDict.t ;
    mutable equivalent_pairs_lr : ProductionPairBoolDict.t ;
    mutable equivalent_pairs_rr : ProductionPairBoolDict.t ;
  }

let create
    (lg:ProbabilisticGrammar.t)
    (rg:ProbabilisticGrammar.t)
  : t =
  {
    left_pgrammar = lg;
    right_pgrammar = rg;
    left_grammar = (ProbabilisticGrammar.get_original lg);
    right_grammar = (ProbabilisticGrammar.get_original rg);
    equivalent_pairs_ll = ProductionPairBoolDict.empty;
    equivalent_pairs_lr = ProductionPairBoolDict.empty;
    equivalent_pairs_rr = ProductionPairBoolDict.empty;
  }

let rec definitionally_equivalent_arb
    (p1_materializer:Production.t -> Production.t)
    (p2_materializer:Production.t -> Production.t)
    (updater:Production.t -> Production.t -> bool -> unit)
    (ppb:ProductionPairBoolDict.t)
    (p1:Production.t)
    (p2:Production.t)
  : bool =
  let definitionally_equivalent_arb =
    definitionally_equivalent_arb
      p1_materializer
      p2_materializer
      updater
  in
  let p1 = p1_materializer p1 in
  let p2 = p2_materializer p2 in
  begin match ProductionPairBoolDict.lookup ppb (p1,p2) with
    | Some b -> b
    | None ->
      let ppb = ProductionPairBoolDict.insert ppb (p1,p2) true in
      let ans =
        begin match (p1,p2) with
          | (Terminal s1,Terminal s2) -> String.equal s1 s2
          | (Concat (p11,p12),Concat (p21,p22)) ->
            (definitionally_equivalent_arb
               ppb
               p11
               p21)
            &&
            (definitionally_equivalent_arb
               ppb
               p12
               p22)
          | (Or (p11,p12),Or (p21,p22)) ->
            (definitionally_equivalent_arb
               ppb
               p11
               p21)
            &&
            (definitionally_equivalent_arb
               ppb
               p12
               p22)
          | (Empty,Empty) -> true
          | _ -> false
        end
      in
      updater p1 p2 ans;
      ans
  end

let definitionally_equivalent_lr
    (l:t)
  : Production.t -> Production.t -> bool =
  definitionally_equivalent_arb
    (Grammar.materialize l.left_grammar)
    (Grammar.materialize l.right_grammar)
    (fun p1 p2 b -> l.equivalent_pairs_lr <- ProductionPairBoolDict.insert l.equivalent_pairs_lr (p1,p2) b)
    l.equivalent_pairs_lr

let definitionally_equivalent_rr
    (l:t)
  : Production.t -> Production.t -> bool =
  definitionally_equivalent_arb
    (Grammar.materialize l.right_grammar)
    (Grammar.materialize l.right_grammar)
    (fun p1 p2 b -> l.equivalent_pairs_rr <- ProductionPairBoolDict.insert l.equivalent_pairs_rr (p1,p2) b)
    l.equivalent_pairs_rr

let definitionally_equivalent_ll
    (l:t)
  : Production.t -> Production.t -> bool =
  definitionally_equivalent_arb
    (Grammar.materialize l.left_grammar)
    (Grammar.materialize l.left_grammar)
    (fun p1 p2 b -> l.equivalent_pairs_ll <- ProductionPairBoolDict.insert l.equivalent_pairs_ll (p1,p2) b)
    l.equivalent_pairs_ll
