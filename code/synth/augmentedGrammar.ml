(*open MyStdLib
open Lang

module Production = struct
  type t =
    | Nonterminal of Id.t * bool
    | Terminal of string
    | Concat of t * t
    | Or of t * t
    | Empty
  [@@deriving bin_io, eq, hash, ord, sexp, show]

  let mk_nonterminal
      (i:Id.t)
      (b:bool)
    : t =
    Nonterminal (i,b)

  let mk_terminal
      (s:string)
    : t =
    Terminal s

  let apply_nonterminal
      (type a)
      ~(f:Id.t -> bool -> a)
      (s:t)
    : a option =
    begin match s with
      | Nonterminal (i,b) -> Some (f i b)
      | _ -> None
    end

  let extract_nonterminal
    : t -> (Id.t * bool) option =
    apply_nonterminal ~f:(curry ident)

  let extract_nonterminal_exn
      (s:t)
    : Id.t * bool =
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

  let mk_concat
      (s1:t)
      (s2:t)
    : t =
    Concat (s1,s2)

  let mk_or
      (s1:t)
      (s2:t)
    : t =
    Or (s1,s2)

  let empty : t = Empty

  let from_base : Grammar.Production.t -> t =
    Grammar.Production.fold
      ~nonterminal_f:(fun i -> mk_nonterminal i true)
      ~terminal_f:(fun s -> mk_terminal s)
      ~concat_f:(fun s1 s2 -> mk_concat s1 s2)
      ~or_f:(fun s1 s2 -> mk_or s1 s2)
      ~empty_f:(empty)
end

module ProdDict = DictOf(Id)(Production)

type t =
  {
    dict  : ProdDict.t ;
    start : Id.t       ;
  }
[@@deriving eq, hash, ord, show]

let start_symbol (g:t) : Id.t = g.start

let get_productions
    (d:t)
    (s:Id.t)
  : Production.t =
  ProdDict.lookup_exn d.dict s

let get_initial_production (d:t) : Production.t =
  get_productions d (start_symbol d)

let add_production (d:t) (s:Id.t) (p:Production.t) =
  let dict =
    ProdDict.insert
      d.dict
      s
      p
  in
  { d with dict = dict }

let update_start (g:t) (start:Id.t) : t =
  { g with start = start }

let initialize (start:Id.t) : t =
  {
    dict  = ProdDict.empty ;
    start = start          ;
  }

let from_base (g:Grammar.t) : t =
  List.fold
    ~f:(fun g (s,ps) ->
        add_production
          g
          s
          (Production.from_base ps))
    ~init:(initialize (Grammar.get_initial_production g))
    (Grammar.symbol_production_list g)

let from_kvp_list_exn
    (rs:(Id.t * Production.t) list)
  : t =
  let (initial,_) = List.hd_exn rs in
  List.fold
    ~f:(fun g (i,ps) -> add_production g i ps)
    ~init:(initialize initial)
   rs
*)
