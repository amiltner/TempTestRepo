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
    | Or of t * t * Float.t
    | Empty
  [@@deriving bin_io, eq, hash, ord, sexp, show]

  let apply_nonterminal
      (type a)
      ~(f:Id.t -> a)
      (s:t)
    : a option =
    begin match s.t_node with
      | Nonterminal i -> Some (f i)
      | _ -> None
    end

  let destruct_nonterminal
    : t -> Id.t option =
    apply_nonterminal ~f:ident

  let destruct_nonterminal_exn
      (s:t)
    : Id.t =
    Option.value_exn (destruct_nonterminal s)

  let apply_terminal
      (type a)
      ~(f:string -> a)
      (s:t)
    : a option =
    begin match s.t_node with
      | Terminal s -> Some (f s)
      | _ -> None
    end

  let destruct_terminal
    : t -> string option =
    apply_terminal ~f:ident

  let destruct_terminal_exn
      (s:t)
    : string =
    Option.value_exn (destruct_terminal s)

  let apply_concat
      (type a)
      ~(f:t -> t -> a)
      (s:t)
    : a option =
    begin match s.t_node with
      | Concat (s1,s2) -> Some (f s1 s2)
      | _ -> None
    end

  let destruct_concat
    : t -> (t * t) option =
    apply_concat ~f:(fun s1 s2 -> (s1,s2))

  let destruct_concat_exn
      (s:t)
    : t * t =
    Option.value_exn (destruct_concat s)

  let apply_or
      (type a)
      ~(f:t -> t -> Float.t -> a)
      (s:t)
    : a option =
    begin match s.t_node with
      | Or (s1,s2,fl) -> Some (f s1 s2 fl)
      | _ -> None
    end

  let destruct_or
    : t -> (t * t * Float.t) option =
    apply_or ~f:(fun s1 s2 f -> (s1,s2,f))

  let destruct_or_exn
      (s:t)
    : t * t * Float.t =
    Option.value_exn (destruct_or s)

  let fold
      (type a)
      ~(nonterminal_f:Id.t -> a)
      ~(terminal_f:string -> a)
      ~(concat_f:a -> a -> a)
      ~(or_f:a -> a -> Float.t -> a)
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
        | Or (s1,s2,f) -> or_f (fold_internal s1) (fold_internal s2) f
        | Empty -> empty_f
      end
    in
    fold_internal s

  let extract_grammar_production
      (p:t)
    : Grammar.Production.t =
    p.original
end

module ProdDict = DictOf(Id)(Production)

type t =
  {
    dict  : ProdDict.t   ;
    start : Production.t         ;
    original : Grammar.t ;
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

let symbol_production_list (g:t) : (Id.t * Production.t) list =
  ProdDict.as_kvp_list g.dict

let initialize (start:Production.t) (original:Grammar.t) : t =
  {
    dict  = ProdDict.empty ;
    start = start          ;
    original = original    ;
  }

let get_original (g:t) : Grammar.t = g.original

let from_kvp_list_exn
    (orig:Grammar.t)
    (start:Production.t)
    (rs:(Id.t * Production.t) list)
  : t =
  List.fold
    ~f:(fun g (i,ps) -> add_production g i ps)
    ~init:(initialize start orig)
    rs

let is_recursive_id
    (g:t)
    (i:Id.t)
  : bool =
  let rec is_recursive_id
      (p:Production.t)
      (processed:Id.t list)
    : bool =
    begin match p.t_node with
      | Nonterminal i' ->
        if Id.equal i i' then
          true
        else if List.mem ~equal:Id.equal processed i' then
          false

        else
          is_recursive_id
            (get_productions g i)
            (i'::processed)
      | Terminal s ->
        false
      | Concat (p1,p2) ->
        (is_recursive_id p1 processed)
        || (is_recursive_id p2 processed)
      | Or (p1,p2,_) ->
        (is_recursive_id p1 processed)
        || (is_recursive_id p2 processed)
      | Empty -> false
    end
  in
  is_recursive_id
    (get_productions g i)
    []

(* Assumes g1 and g2 have the same underlying grammar. *)
let kl_divergence
    (g1:t)
    (g2:t)
  : Float.t =
  let rec get_terminal_probabilities
      (g:t)
      (incoming:Float.t)
      (p:Production.t)
    : Float.t list =
    begin match p.t_node with
      | Empty ->
        if not ((Float.equal incoming 0.) || (Float.equal incoming 1.)) then
          failwith "ahhh"
        else
          [0.]
      | Nonterminal i ->
        get_terminal_probabilities
          g
          incoming
          (get_productions g i)
      | Terminal s -> [incoming]
      | Concat (p1,p2) ->
        let ps1 =
          get_terminal_probabilities
            g
            incoming
            p1
        in
        let ps2 =
          get_terminal_probabilities
            g
            incoming
            p2
        in
        cartesian_map
          ~f:( *. )
          ps1
          ps2
      | Or (p1,p2,f) ->
        let ps1 =
          get_terminal_probabilities
            g
            (incoming *. f)
            p1
        in
        let ps2 =
          get_terminal_probabilities
            g
            (incoming *. (Probability.not f))
            p1
        in
        ps1 @ ps2
    end
  in
  let g1_probabilities =
    get_terminal_probabilities
      g1
      1.
      (get_initial_production g1)
  in
  let g2_probabilities =
    get_terminal_probabilities
      g2
      1.
      (get_initial_production g2)
  in
  if not (List.length g1_probabilities = List.length g2_probabilities) then
    (print_endline (show g1); print_endline (show g2) );
  let probability_pairs =
    List.map2_exn
      ~f:(fun p1 p2 -> p1 *. Math.log(p1 /. p2))
      g1_probabilities
      g2_probabilities
  in
  FloatList.sum probability_pairs

let entropy
    (pg:t)
  : Float.t =
  let kvps = symbol_production_list pg in
  let eqns =
    List.map
      ~f:(fun (s,p) ->
          let p_eqn =
            Production.fold
              ~nonterminal_f:SystemOfEquations.mk_variable
              ~terminal_f:(func_of SystemOfEquations.zero)
              ~concat_f:SystemOfEquations.sum
              ~or_f:(fun s1 s2 p ->
                  let create_from_prob
                      (p:Float.t)
                      (s:SystemOfEquations.t)
                    : SystemOfEquations.t =
                    let neglogp = Float.neg (Math.log2 p) in
                    let sum =
                      SystemOfEquations.sum
                        s
                        (SystemOfEquations.mk_constant neglogp)
                    in
                    SystemOfEquations.scale
                      sum
                      p
                  in
                  let left = create_from_prob p s1 in
                  let right = create_from_prob (1. -. p) s2 in
                  SystemOfEquations.sum
                    left
                    right)
              ~empty_f:SystemOfEquations.zero
              p
          in
          let lhs_eqn =
            SystemOfEquations.neg
              (SystemOfEquations.mk_variable s)
          in
          SystemOfEquations.sum
            p_eqn
            lhs_eqn)
      kvps
  in
  let soln =
    SystemOfEquations.solve
      eqns
  in
  Production.fold
    ~nonterminal_f:(List.Assoc.find_exn ~equal:Id.equal soln)
    ~terminal_f:(func_of 0.)
    ~concat_f:(+.)
    ~or_f:(fun e1 e2 p -> failwith "todo")
    ~empty_f:(0.)
    pg.start

let kl_divergence
    (g1:t)
    (g2:t)
  : Float.t option =
  let kvps =
    List.map2_exn
      ~f:(fun (s1,p1) (s2,p2) ->
          assert (Id.equal s1 s2);
          (s1,p1,p2))
      (symbol_production_list g1)
      (symbol_production_list g2)
  in
  let eqns =
    List.map
      ~f:(fun (s,p,q) ->
          let rec to_p_eqn
              (p:Production.t)
              (q:Production.t)
            : SystemOfEquations.t option =
            begin match p.t_node with
              | Nonterminal s -> Some (SystemOfEquations.mk_variable s)
              | Terminal s -> Some (SystemOfEquations.zero)
              | Concat (p1,p2) ->
                let (q1,q2) = Production.destruct_concat_exn q in
                let left = to_p_eqn p1 q1 in
                let right = to_p_eqn p2 q2 in
                begin match (left,right) with
                  | (Some left, Some right) -> 
                    Some
                      (SystemOfEquations.sum
                         left
                         right)
                  | _ -> None
                end
              | Or (p1,p2,pf) ->
                let (q1,q2,qf) = Production.destruct_or_exn q in
                let create_from_prob
                    (p:Float.t)
                    (q:Float.t)
                    (s:SystemOfEquations.t)
                  : SystemOfEquations.t option =
                  if Float.equal q 0. && not (Float.equal p 0.) then
                    None
                  else
                    let log2pq =
                      if Float.equal p 0. then
                        0.
                      else
                        Math.log2 (p /. q)
                    in
                    let sum =
                      SystemOfEquations.sum
                        s
                        (SystemOfEquations.mk_constant log2pq)
                    in
                    Some
                      (SystemOfEquations.scale
                         sum
                         p)
                in
                let left = to_p_eqn p1 q1 in
                let right = to_p_eqn p2 q2 in
                begin match (left,right) with
                  | (Some left, Some right) ->
                    let left =
                      create_from_prob
                        pf
                        qf
                        left
                    in
                    let right =
                      create_from_prob
                        (Probability.not pf)
                        (Probability.not qf)
                        right
                    in
                    begin match (left,right) with
                      | (Some left, Some right) ->
                        Some
                          (SystemOfEquations.sum
                             left
                             right)
                      | _ -> None
                    end
                  | _ -> None
                end
              | Empty -> Some SystemOfEquations.zero
            end
          in
          begin match to_p_eqn p q with
            | None -> None
            | Some p_eqn ->
              let lhs_eqn =
                SystemOfEquations.neg
                  (SystemOfEquations.mk_variable s)
              in
              Some
                (SystemOfEquations.sum
                   p_eqn
                   lhs_eqn)
          end)
      kvps
  in
  let eqns_o = distribute_option eqns in
  begin match eqns_o with
    | None -> None
    | Some eqns ->
      let soln =
        SystemOfEquations.solve
          eqns
      in
      let rec retrieve_dat
          (p1:Production.t)
          (p2:Production.t)
        : Float.t =
        begin match (p1.t_node,p2.t_node) with
          | (Nonterminal s,_) -> List.Assoc.find_exn ~equal:Id.equal soln s
          | (Terminal s,_) -> 0.
          | (Concat (p11,p12), Concat (p21,p22)) ->
            (retrieve_dat p11 p21) +. (retrieve_dat p12 p22)
          | (Or (f1,p11,p12), Or (f2,p21,p22)) ->
            failwith "todo"
          | _ -> failwith "todo"
        end
      in
      Some
        (retrieve_dat
           g1.start
           g2.start)
  end

let is_nonempty_production
    (g:t)
    (p:Production.t)
  : bool =
  let is_nonempty_with_priors
      (map:(Id.t * bool) list)
    : Production.t -> bool =
    Production.fold
      ~nonterminal_f:(List.Assoc.find_exn ~equal:Id.equal map)
      ~terminal_f:(func_of true)
      ~concat_f:(&&)
      ~or_f:(fun b1 b2 f -> b1 || b2)
      ~empty_f:false
  in
  let map =
    List.map
      ~f:(fun (i,_) -> (i,false))
      (symbol_production_list g)
  in
  let map =
    fold_until_completion
      ~f:(fun map ->
         let (updated,map) =
           List.fold
             ~f:(fun (updated,new_map) (i,b) ->
                 if b then
                   (false,(i,b)::new_map)
                 else
                   let b = is_nonempty_with_priors map (get_productions g i) in
                   (b||updated,(i,b)::new_map))
             ~init:(false,[])
             map
         in
         if updated then
           Left map
         else
           Right map)
      map
  in
  is_nonempty_with_priors map p

let is_nonempty
    (g:t)
  : bool =
  is_nonempty_production g (get_initial_production g)

let rec materialize
    (g:t)
    (p:Production.t)
  : Production.t =
  begin match p.t_node with
    | Nonterminal v -> materialize g (get_productions g v)
    | _ -> p
  end

let get_all_subproductions
    (g:t)
  : Production.t -> Production.t list =
  let rec get_all_productions_internal
      (acc:Production.t list)
      (p:Production.t)
    : Production.t list =
    if List.mem ~equal:Production.equal acc p then
      acc
    else
      let acc = p::acc in
      begin match p.t_node with
        | Nonterminal i ->
          get_all_productions_internal acc (get_productions g i)
        | Terminal s -> acc
        | Concat (p1,p2) ->
          let acc = get_all_productions_internal acc p1 in
          get_all_productions_internal acc p2
        | Or (p1,p2,_) ->
          let acc = get_all_productions_internal acc p1 in
          get_all_productions_internal acc p2
        | Empty ->
          acc
      end
  in
  get_all_productions_internal
    []
