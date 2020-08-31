open MyStdLib
module Skele = Skeleton
open Lang
module Skeleton = Skele

type sequence_set =
  | Const of string
  | OrChoice of bool * sequence_set
  | Concat of sequence_set * sequence_set
  | Fix of Id.t * Grammar.Production.t * t
  | OneOf of sequence_set list
  | Apply of Id.t * Id.t
  | Direct of Id.t
  | Unset

and t = (Skeleton.conjunct * sequence_set) list
[@@deriving eq, hash, ord, show]

module Context = struct
  type t = int

  let is_modulo_recursive
      (c:t)
      (g:Grammar.t)
      (p:Grammar.Production.t)
    : bool =
    failwith "ah"

  let peel_recursions
      (c:t)
    : (Id.t * Skeleton.t) list =
    failwith "ah"

  let add_fix
      (c:t)
      (i:Id.t)
      (p:Grammar.Production.t)
    : t =
    failwith "ah"

  let extract_app
      (c:t)
    : (Id.t * Id.t) =
    failwith "ah"
end

let mk_or_choice
    (b:bool)
    (ss:sequence_set)
  : sequence_set =
  OrChoice (b,ss)

let mk_concat
    (ss1:sequence_set)
    (ss2:sequence_set)
  : sequence_set =
  Concat (ss1,ss2)

let unset : sequence_set = Unset

let mk_const
    (s:string)
  : sequence_set =
  Const s

let merge
    (ss1:t)
    (ss2:t)
  : t option =
  failwith "ah"

let mk_fix
    (i:Id.t)
    (p:Grammar.Production.t)
    (underlying:t)
  : sequence_set =
  failwith "ah"

let rec find
    (c:Context.t)
    (l:GrammarLinker.t)
    (pt:ParseTree.t)
    (s:Skeleton.t)
    (g:Grammar.t)
  : t list =
  let rec find_internal
      (c:Context.t)
      (pt:ParseTree.t)
      (p:Grammar.Production.t)
      (incoming:sequence_set -> t)
    : t list =
    let p = Grammar.concretify g p in
    let create_fix =
      if Context.is_modulo_recursive c g p then
        let recs = Context.peel_recursions c in
        List.concat_map
          ~f:(fun (i,s) ->
              let c = Context.add_fix c i p in
              let ts =
                find
                  c
                  l
                  pt
                  s
                  g
              in
              List.map
                ~f:(incoming % (mk_fix i p))
                ts)
          recs
      else
        []
    in
    let create_use_context =
      (Context.extract_apps c)@(Context.extract_matching c)
    in
    let syntactics =
      begin match pt with
        | Or (b,pt) ->
          let (p1,p2) = Grammar.Production.extract_or_exn p in
          let p = if b then p1 else p2 in
          find_internal c pt p (incoming % (mk_or_choice b))
        | Concat (pt1,pt2) ->
          let (p1,p2) = Grammar.Production.extract_concat_exn p in
          let ss1 = find_internal c pt1 p1 (incoming % (Fn.flip mk_concat unset)) in
          let ss2 = find_internal c pt2 p2 (incoming % (mk_concat unset)) in
          cartesian_filter_map
            merge
            ss1
            ss2
        | Terminal s ->
          [incoming (mk_const s)]
      end
    in
    create_fix@syntactics
  in
  let Disjunct conjuncts = s in
  let conjuncts_splits =
    all_peels_split
      conjuncts
  in
  List.concat_map
    ~f:(fun (c1s,c,c2s) ->
        let t1s = List.map ~f:(fun t -> (t,unset)) c1s in
        let t2s = List.map ~f:(fun t -> (t,unset)) c2s in
        find_internal
          (failwith "ah")
          pt
          (Grammar.get_initial_production g)
          (fun t -> t1s@((c,t)::t2s)))
    conjuncts_splits

