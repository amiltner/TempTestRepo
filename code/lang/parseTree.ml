open MyStdLib

type t =
  | Or of bool * t
  | Concat of t * t
  | Terminal of string
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

let mk_terminal
    (s:string)
  : t =
  Terminal s

let apply_terminal
    (type a)
    ~(f:string -> a)
    (p:t)
  : a option =
  begin match p with
    | Terminal s -> Some (f s)
    | _ -> None
  end

let destruct_terminal
  : t -> string option =
  apply_terminal ~f:ident

let destruct_terminal_exn
    (p:t)
  : string =
  Option.value_exn (destruct_terminal p)

let fold
    (type a)
    ~(or_f:bool -> a -> a)
    ~(concat_f:a -> a -> a)
    ~(terminal_f:string -> a)
  : t -> a =
  let rec fold
      (p:t)
    : a =
    begin match p with
      | Or (b,p) ->
        or_f b (fold p)
      | Concat (p1,p2) ->
        concat_f (fold p1) (fold p2)
      | Terminal s -> terminal_f s
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
      | Terminal s -> (Terminal s,bs)
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

let to_string
  : t -> string =
  fold
    ~or_f:(func_of ident)
    ~concat_f:(^)
    ~terminal_f:ident

let to_bool_list
  : t -> bool list =
  fold
    ~or_f:(List.cons)
    ~concat_f:(@)
    ~terminal_f:(func_of [])
