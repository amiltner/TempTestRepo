open MyStdLib

module Production = struct
  type t =
    | Nonterminal of Id.t
    | Terminal of string
    | Concat of t * t
    | Or of t * t
    | Empty
  [@@deriving bin_io, eq, hash, ord, sexp, show]

  let mk_nonterminal
      (i:Id.t)
    : t =
    Nonterminal i

  let mk_terminal
      (s:string)
    : t =
    Terminal s

  let mk_or
      (p1:t)
      (p2:t)
    : t =
    Or (p1,p2)

  let mk_concat
      (p1:t)
      (p2:t)
    : t =
    Concat (p1,p2)

  let empty : t = Empty

  let apply_nonterminal
      (type a)
      ~(f:Id.t -> a)
      (s:t)
    : a option =
    begin match s with
      | Nonterminal i -> Some (f i)
      | _ -> None
    end

  let extract_nonterminal
    : t -> Id.t option =
    apply_nonterminal ~f:ident

  let extract_nonterminal_exn
      (s:t)
    : Id.t =
    Option.value_exn (extract_nonterminal s)

  let apply_terminal
      (type a)
      ~(f:string -> a)
      (s:t)
    : a option =
    begin match s with
      | Terminal s -> Some (f s)
      | _ -> None
    end

  let extract_terminal
    : t -> string option =
    apply_terminal ~f:ident

  let extract_terminal_exn
      (s:t)
    : string =
    Option.value_exn (extract_terminal s)

  let apply_concat
      (type a)
      ~(f:t -> t -> a)
      (s:t)
    : a option =
    begin match s with
      | Concat (c1,c2) -> Some (f c1 c2)
      | _ -> None
    end

  let extract_concat
    : t -> (t * t) option =
    apply_concat ~f:(Tuple.T2.create)

  let extract_concat_exn
      (s:t)
    : t * t =
    Option.value_exn (extract_concat s)

  let apply_or
      (type a)
      ~(f:t -> t -> a)
      (s:t)
    : a option =
    begin match s with
      | Or (c1,c2) -> Some (f c1 c2)
      | _ -> None
    end

  let extract_or
    : t -> (t * t) option =
    apply_or ~f:(Tuple.T2.create)

  let extract_or_exn
      (s:t)
    : t * t =
    Option.value_exn (extract_or s)

  let fold
      (type a)
      ~(nonterminal_f:Id.t -> a)
      ~(terminal_f:string -> a)
      ~(concat_f:a -> a -> a)
      ~(or_f:a -> a -> a)
      ~(empty_f:a)
      (s:t)
    : a =
    let rec fold_internal
        (s:t)
      : a =
      begin match s with
        | Nonterminal i -> nonterminal_f i
        | Terminal s -> terminal_f s
        | Concat (s1,s2) -> concat_f (fold_internal s1) (fold_internal s2)
        | Or (s1,s2) -> or_f (fold_internal s1) (fold_internal s2)
        | Empty -> empty_f
      end
    in
    fold_internal s
end

module ProdDict = DictOf(Id)(Production)

type t =
  {
    dict  : ProdDict.t ;
    start : Production.t       ;
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

let update_start (g:t) (p:Production.t) : t =
  { g with start = p }

let symbol_production_list (g:t) : Production.t * ((Id.t * Production.t) list) =
  let start = g.start in
  let list = ProdDict.as_kvp_list g.dict in
  (start,list)

let initialize (start:Production.t) : t =
  {
    dict  = ProdDict.empty ;
    start = start          ;
  }

let from_kvp_list_exn
    (start:Production.t)
    (rs:(Id.t * Production.t) list)
  : t =
  List.fold
    ~f:(fun g (i,ps) -> add_production g i ps)
    ~init:(initialize start)
    rs

let rec materialize
    (g:t)
    (p:Production.t)
  : Production.t =
  begin match p with
    | Nonterminal v -> materialize g (get_productions g v)
    | _ -> p
  end

let is_recursive_production_modulo
    (g:t)
    (modulo:Production.t list)
    (search:Production.t)
  : bool =
  let rec is_recursive_production_modulo
      (p:Production.t)
      (processed:Production.t list)
    : bool =
    if Production.equal p search && not (List.is_empty processed) then
      true
    else if List.mem ~equal:Production.equal processed p then
      false
    else if List.mem ~equal:Production.equal modulo p then
      false
    else
      let processed = p::processed in
      begin match p with
        | Nonterminal i ->
          is_recursive_production_modulo
            (get_productions g i)
            processed
        | Terminal s ->
          false
        | Concat (p1,p2) ->
          (is_recursive_production_modulo p1 processed)
          || (is_recursive_production_modulo p2 processed)
        | Or (p1,p2) ->
          (is_recursive_production_modulo p1 processed)
          || (is_recursive_production_modulo p2 processed)
        | Empty -> false
      end
  in
  is_recursive_production_modulo
    search
    []

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
      begin match p with
        | Nonterminal i ->
          get_all_productions_internal acc (get_productions g i)
        | Terminal s -> acc
        | Concat (p1,p2) ->
          let acc = get_all_productions_internal acc p1 in
          get_all_productions_internal acc p2
        | Or (p1,p2) ->
          let acc = get_all_productions_internal acc p1 in
          get_all_productions_internal acc p2
        | Empty ->
          acc
      end
  in
  get_all_productions_internal
    []

let retrieve_necessary_productions
    (g:t)
  : Id.t list =
  let rec retrieve_necessary_productions
      (p:Production.t)
      (processed:Id.t list)
    : Id.t list =
    begin match p with
      | Nonterminal i ->
        if List.mem ~equal:Id.equal processed i then
          processed
        else
          retrieve_necessary_productions (get_productions g i) (i::processed)
      | Terminal s -> processed
      | Concat (p1,p2) ->
        let processed =
          retrieve_necessary_productions
            p1
            processed
        in
        retrieve_necessary_productions
          p2
          processed
      | Or (p1,p2) ->
        let processed =
          retrieve_necessary_productions
            p1
            processed
        in
        retrieve_necessary_productions
          p2
          processed
      | Empty -> processed
    end
  in
  retrieve_necessary_productions
    g.start
    []

let remove_unnecessary_productions
    (g:t)
  : t =
  let necessary_ids = retrieve_necessary_productions g in
  let kvps = ProdDict.as_kvp_list g.dict in
  let kvps =
    List.filter
      ~f:((List.mem ~equal:Id.equal necessary_ids) % fst)
      kvps
  in
  let dict = ProdDict.from_kvp_list kvps in
  { g with
    dict = dict; }

let minify
  (g:t)
  : t =
  let rec minify
      (g:t)
      (processed:Id.t list)
    : t =
    let p = g.start in
    begin match p with
      | Nonterminal i ->
        if List.mem ~equal:Id.equal processed i then
          g
        else if is_recursive_production_modulo
            g
            (List.map ~f:Production.mk_nonterminal processed)
            p then
          let prod = get_productions g i in
          let g = update_start g prod in
          let g =
            minify
              g
              (i::processed)
          in
          let dict = g.dict in
          let dict =
            ProdDict.insert
              dict
              i
              g.start
          in
          {
            dict = dict;
            start = p;
          }
        else
          let prod = get_productions g i in
          let g = update_start g prod in
          minify
            g
            processed
      | Terminal s ->
        g
      | Concat (p1,p2) ->
        let g1 = minify (update_start g p1) processed in
        let g2 = minify (update_start g1 p2) processed in
        let p1 = g1.start in
        let p2 = g2.start in
        {
          start = Production.mk_concat p1 p2 ;
          dict = g2.dict ;
        }
      | Or (p1,p2) ->
        let g1 = minify (update_start g p1) processed in
        let g2 = minify (update_start g1 p2) processed in
        let p1 = g1.start in
        let p2 = g2.start in
        {
          start = Production.mk_or p1 p2 ;
          dict = g2.dict ;
        }
      | Empty -> g
    end
  in
  remove_unnecessary_productions (minify g [])

let rewrites
    (g:t)
  : t list =
  let rec rewrites
      (g:t)
      (processed:Id.t list)
    : t list * Id.t list =
    let p = g.start in
    begin match p with
      | Nonterminal i ->
        let prod = get_productions g i in
        let current_rewrite = update_start g prod in
        let prod = get_productions g i in
        let g = update_start g prod in
        let sub_rewrites =
          if List.mem ~equal:Id.equal processed i then
            []
          else
            let (gs,processed) =
              rewrites
                g
                (i::processed)
            in
            List.map
              ~f:(fun g ->
                  let dict = g.dict in
                  let dict =
                    ProdDict.insert
                      dict
                      i
                      g.start
                  in
                  {
                    dict = dict;
                    start = p;
                  })
              gs
        in
        (current_rewrite::sub_rewrites,i::processed)
      | Terminal s ->
        ([],processed)
      | Concat (p1,p2) ->
        let (g1s,processed) = rewrites (update_start g p1) processed in
        let (g2s,processed) = rewrites (update_start g p2) processed in
        let left_rewrites =
          List.map
            ~f:(fun g1 ->
                let p1 = g1.start in
                {
                  start = Production.mk_concat p1 p2 ;
                  dict = g1.dict ;
                })
            g1s
        in
        let right_rewrites =
          List.map
            ~f:(fun g2 ->
                let p2 = g2.start in
                {
                  start = Production.mk_concat p1 p2 ;
                  dict = g2.dict ;
                })
            g2s
        in
        (left_rewrites@right_rewrites,processed)
      | Or (p1,p2) ->
        let (g1s,processed) = rewrites (update_start g p1) processed in
        let (g2s,processed) = rewrites (update_start g p2) processed in
        let left_rewrites =
          List.map
            ~f:(fun g1 ->
                let p1 = g1.start in
                {
                  start = Production.mk_or p1 p2 ;
                  dict = g1.dict ;
                })
            g1s
        in
        let right_rewrites =
          List.map
            ~f:(fun g2 ->
                let p2 = g2.start in
                {
                  start = Production.mk_or p1 p2 ;
                  dict = g2.dict ;
                })
            g2s
        in
        (left_rewrites@right_rewrites,processed)
      | Empty -> ([],processed)
    end
  in
  fst (rewrites g [])

let rec concretify
    (g:t)
    (p:Production.t)
  : Production.t =
  begin match Production.extract_nonterminal p with
    | None -> p
    | Some i -> concretify g (get_productions g i)
  end
