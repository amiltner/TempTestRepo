open MyStdLib

type t =
  | Or of bool * t
  | Concat of t * t
  | Union of t * t
  | Unrestricted
[@@deriving eq, hash, ord, show]

let mk_or
    (b:bool)
    (p:t)
  : t =
  Or (b,p)

let apply_or
    (type a)
    ~(f:bool -> t -> a)
    (p:t)
  : a option =
  begin match p with
    | Or (b,p) -> Some (f b p)
    | _ -> None
  end

let destruct_or
  : t -> (bool * t) option =
  apply_or ~f:(fun b p -> (b,p))

let destruct_or_exn
    (p:t)
  : bool * t =
  Option.value_exn (destruct_or p)

let mk_concat
    (p1:t)
    (p2:t)
  : t =
  Concat (p1,p2)

let apply_concat
    (type a)
    ~(f:t -> t -> a)
    (p:t)
  : a option =
  begin match p with
    | Concat (p1,p2) -> Some (f p1 p2)
    | _ -> None
  end

let destruct_concat
  : t -> (t * t) option =
  apply_concat ~f:(fun p1 p2 -> (p1,p2))

let destruct_concat_exn
    (p:t)
  : t * t =
  Option.value_exn (destruct_concat p)

let mk_unrestricted
  : t =
  Unrestricted

let mk_union
    (p1o:t option)
    (p2o:t option)
  : t option =
  let rec mk_union
      (p1:t)
      (p2:t)
    : t =
    begin match (p1,p2) with
      | (Unrestricted, _) -> Unrestricted
      | (_, Unrestricted) -> Unrestricted
      | (Union (p11,p12), Or (b,p)) ->
        if b then
          Union ((mk_union p11 p),p12)
        else
          Union (p11,(mk_union p12 p))
      | (Or _, Union _) ->
        mk_union p2 p1
      | (Concat (p11,p12), Concat (p21,p22)) ->
        mk_concat (mk_union p11 p21) (mk_union p12 p22)
      | (Or (b1,p1), Or (b2,p2)) ->
        begin match (b1,b2) with
          | (true,true) ->
            Or (true, mk_union p1 p2)
          | (true,false) ->
            Union (p1,p2)
          | (false,true) ->
            Union (p2,p1)
          | (false,false) ->
            Or (false,mk_union p1 p2)
        end
      | _ -> failwith "shouldnt happen"
    end
  in
  begin match (p1o,p2o) with
    | (None,None) -> None
    | (None,Some p2) -> Some p2
    | (Some p1,None) -> Some p1
    | (Some p1, Some p2) -> Some (mk_union p1 p2)
  end

let doublebind
    (type a)
    ~(f:t -> t -> a option)
    (p1o:t option)
    (p2o:t option)
  : a option =
  begin match (p1o,p2o) with
    | (Some p1, Some p2) -> f p1 p2
    | _ -> None
  end

let mk_intersect
    (p1o:t option)
    (p2o:t option)
  : t option =
  let rec mk_intersect
      (p1:t)
      (p2:t)
    : t option =
    begin match (p1,p2) with
      | (Unrestricted, _) -> Some p2
      | (_, Unrestricted) -> Some p1
      | (Union (p11,p12), Or (b,p)) ->
        if b then
          let p1o = mk_intersect p11 p in
          Option.map ~f:(mk_or b) p1o
        else
          let p2o = mk_intersect p12 p in
          Option.map ~f:(mk_or b) p2o
      | (Or _, Union _) ->
        mk_intersect p2 p1
      | (Union (p11,p12), Union (p21,p22)) ->
        let p1o = mk_intersect p11 p21 in
        let p2o = mk_intersect p12 p22 in
        begin match (p1o,p2o) with
          | (None,None) -> None
          | (Some p1, None) -> Some (mk_or true p1)
          | (None, Some p2) -> Some (mk_or false p2)
          | (Some p1, Some p2) -> Some (Union (p1,p2))
        end
      | (Concat (p11,p12), Concat (p21,p22)) ->
        let p1o = mk_intersect p11 p21 in
        let p2o = mk_intersect p12 p22 in
        doublebind ~f:(Option.some %% mk_concat) p1o p2o
      | (Or (b1,p1), Or (b2,p2)) ->
        if b1 = b2 then
          let po = mk_intersect p1 p2 in
          Option.map ~f:(mk_or b1) po
        else
          None
      | _ -> failwith "shouldnt happen"
    end
  in
  doublebind mk_intersect p1o p2o

let fold
    (type a)
    ~(or_f:bool -> a -> a)
    ~(concat_f:a -> a -> a)
    ~(union_f:a -> a -> a)
    ~(terminal_f:string -> a)
    ~(unrestricted_f:a)
  : t -> a =
  let rec fold
      (p:t)
    : a =
    begin match p with
      | Or (b,p) ->
        or_f b (fold p)
      | Concat (p1,p2) ->
        concat_f (fold p1) (fold p2)
      | Unrestricted -> unrestricted_f
      | Union (p1,p2) ->
        union_f (fold p1) (fold p2)
    end
  in
  fold

let from_bool_list
    (g:Grammar.t)
    (bs:bool list)
  : t =
  let rec to_parse_tree
      (p:Grammar.Production.t)
      (bs:bool list)
    : t * bool list =
    begin match p with
      | Nonterminal i ->
        to_parse_tree
          (Grammar.get_productions g i)
          bs
      | Terminal s -> (Unrestricted,bs)
      | Concat (p1,p2) ->
        let (pt1,bs) =
          to_parse_tree
            p1
            bs
        in
        let (pt2,bs) =
          to_parse_tree
            p2
            bs
        in
        (Concat (pt1,pt2),bs)
      | Or (p1,p2) ->
        let (b,bs) = split_by_first_exn bs in
        let (pt,bs) =
          if b then
            to_parse_tree
              p1
              bs
          else
            to_parse_tree
              p2
              bs
        in
        (Or(b,pt),bs)
      | Empty -> failwith "cannot happen"
    end
  in
  let (pt,bs) =
    to_parse_tree
      (Grammar.get_initial_production g)
      bs
  in
  assert (List.length bs = 0);
  pt

let from_parse_tree
  : ParseTree.t -> t =
  ParseTree.fold
    ~or_f:mk_or
    ~concat_f:mk_concat
    ~terminal_f:(func_of mk_unrestricted)
