open MyStdLib
open Lang

type t =
  | EmptyFunc
  | StringIntro of string
  | OrElim of Id.t * Id.t * t * t
  | ConcatElim of Id.t * Id.t * Id.t * t
  | OrIntro of (bool * t)
  | ConcatIntro of t * t
  | Variable of Id.t
  | Apply of Id.t * Id.t
  | Fix of Id.t * Id.t * t
[@@deriving eq, hash, ord, show]

let mk_or_intro
    (choice:bool)
    (inner:t)
  : t =
  OrIntro (choice,inner)

let mk_concat_intro
    (c1:t)
    (c2:t)
  : t =
  ConcatIntro (c1,c2)

let mk_or_elim
    (old_i:Id.t)
    (new_i:Id.t)
    (c1:t)
    (c2:t)
  : t =
  OrElim (old_i,new_i,c1,c2)

let mk_concat_elim
    (old_i:Id.t)
    (i1:Id.t)
    (i2:Id.t)
    (inner:t)
  : t =
  ConcatElim (old_i,i1,i2,inner)

let empty_func : t = EmptyFunc

let mk_string_intro
    (s:string)
  : t =
  StringIntro s

let mk_variable
    (v:Id.t)
  : t =
  Variable v

let mk_apply
    (f:Id.t)
    (v:Id.t)
  : t =
  Apply (f,v)

let mk_fix
    (fid:Id.t)
    (cid:Id.t)
    (c:t)
  : t =
  Fix (fid,cid,c)

let fold
    (type a)
    ~(empty_func:a)
    ~(string_intro:string -> a)
    ~(or_elim:Id.t -> Id.t -> a -> a -> a)
    ~(concat_elim:Id.t -> Id.t -> Id.t -> a -> a)
    ~(or_intro:bool -> a -> a)
    ~(concat_intro:a -> a -> a)
    ~(variable:Id.t -> a)
    ~(apply:Id.t -> Id.t -> a)
    ~(fix:Id.t -> Id.t -> a -> a)
  : t -> a =
  let rec fold_internal
      (s:t)
    : a =
    begin match s with
      | EmptyFunc -> empty_func
      | StringIntro s -> string_intro s
      | OrElim (i1,i2,c1,c2) ->
        or_elim i1 i2 (fold_internal c1) (fold_internal c2)
      | ConcatElim (i1,i2,i3,c) ->
        concat_elim i1 i2 i3 (fold_internal c)
      | OrIntro (b,c) ->
        or_intro b (fold_internal c)
      | ConcatIntro (c1,c2) ->
        concat_intro (fold_internal c1) (fold_internal c2)
      | Variable i -> variable i
      | Apply (i1,i2) -> apply i1 i2
      | Fix (i1,i2,c) -> fix i1 i2 (fold_internal c)
    end
  in
  fold_internal

let size : t -> int =
  fold
    ~empty_func:1
    ~string_intro:(fun _ -> 1)
    ~or_elim:(fun _ _ i1 i2 -> i1+i2+3)
    ~concat_elim:(fun _ _ _ i -> i+4)
    ~or_intro:(fun _ i -> i+2)
    ~concat_intro:(fun i1 i2 -> i1+i2+1)
    ~variable:(fun _ -> 1)
    ~apply:(fun _ _ -> 2)
    ~fix:(fun _ _ i -> i+3)

let nested_fix : t -> bool =
  fst %
  (fold
     ~empty_func:(false,false)
     ~string_intro:(fun _ -> (false,false))
     ~or_elim:(fun _ _ (b11,b12) (b21,b22) -> (b11 || b21,b12||b22))
     ~concat_elim:(fun _ _ _ bs -> bs)
     ~or_intro:(fun _ bs -> bs)
     ~concat_intro:(fun (b11,b12) (b21,b22) -> (b11 || b21,b12||b22))
     ~variable:(fun _ -> (false,false))
     ~apply:(fun _ _ -> (false,false))
     ~fix:(fun _ _ (b11,b12) -> (b11 || b12,true)))

let is_applied
    (i:Id.t)
  : t -> bool =
  fold
    ~empty_func:false
    ~string_intro:(fun _ -> false)
    ~or_elim:(fun _ _ b1 b2 -> b1 || b2)
    ~concat_elim:(fun _ _ _ b -> b)
    ~or_intro:(fun _ b -> b)
    ~concat_intro:(fun b1 b2 -> b1 || b2)
    ~variable:(fun _ -> false)
    ~apply:(fun fi _ -> Id.equal fi i)
    ~fix:(fun _ _ b -> b)

module IdParseTreeMap = DictOf(Id)(ParseTree)
module IdParsePreImageMap = DictOf(Id)(OptionOf(ParsePreImage))

(* THIS IS VERY WRONG, MAKING A UNION ON ONE VAR DOESNT UNION ALL VARS *)
let get_preimage
    (p:ParseTree.t)
    (c:t)
  : ParsePreImage.t option =
  let get_var_preimage
      (ps:IdParsePreImageMap.t)
      (i:Id.t)
    : ParsePreImage.t option =
    IdParsePreImageMap.lookup_default
      ~default:(Some ParsePreImage.mk_unrestricted)
      ps
      i
  in
  let rec get_preimage
      (ctx:IdParseTreeMap.t)
      (p:ParseTree.t)
      (c:t)
    : IdParsePreImageMap.t =
    begin match c with
      | EmptyFunc -> failwith "invalid"
      | StringIntro s ->
        IdParsePreImageMap.empty
      | OrElim (i1,i2,c1,c2) ->
        let pt1 = IdParseTreeMap.lookup_exn ctx i1 in
        let (b,pt2) = ParseTree.destruct_or_exn pt1 in
        let ctx =
          IdParseTreeMap.insert
            ctx
            i2
            pt2
        in
        let image_ctx =
          if b then
            get_preimage
              ctx
              p
              c1
          else
            get_preimage
              ctx
              p
              c2
        in
        let i2_image = get_var_preimage image_ctx i2 in
        let i1_image = get_var_preimage image_ctx i1 in
        let i1_i2_restriction = Option.map ~f:(ParsePreImage.mk_or b) i2_image in
        let i1_image = ParsePreImage.mk_intersect i1_image i1_i2_restriction in
        IdParsePreImageMap.insert
          image_ctx
          i1
          i1_image
      | ConcatElim (i1,i2,i3,c) ->
        let pt1 =
          IdParseTreeMap.lookup_exn
            ctx
            i1
        in
        let (pt2,pt3) = ParseTree.destruct_concat_exn pt1 in
        let ctx =
          IdParseTreeMap.insert
            (IdParseTreeMap.insert
               ctx
               i2
               pt2)
            i3
            pt3
        in
        let image_ctx =
          get_preimage
            ctx
            p
            c
        in
        let i1_image = get_var_preimage image_ctx i1 in
        let i2_image = get_var_preimage image_ctx i2 in
        let i3_image = get_var_preimage image_ctx i3 in
        let i1_i2i3_restriction =
          ParsePreImage.doublebind
            ~f:(Option.some %% ParsePreImage.mk_concat)
            i2_image
            i3_image
        in
        let i1_image =
          ParsePreImage.mk_intersect
            i1_image
            i1_i2i3_restriction
        in
        IdParsePreImageMap.insert
          image_ctx
          i1
          i1_image
      | OrIntro (b1,c) ->
        let (b2,p) = ParseTree.destruct_or_exn p in
        if b1 = b2 then
          failwith "poops"
        else
          let ids = IdParseTreeMap.key_list ctx in
          let kvps =
            List.map
              ~f:(fun k -> (k,None))
              ids
          in
          IdParsePreImageMap.from_kvp_list kvps
      | _ ->
        failwith "invalid"
        (*
          | OrIntro of (bool * t)
          | ConcatIntro of t * t
          | Variable of Id.t
          | Apply of Id.t * Id.t
          | Fix of Id.t * Id.t * t*)
    end
  in
  get_var_preimage
    (get_preimage
       (IdParseTreeMap.singleton (Id.from_int 0) p)
       p
       c)
    (Id.from_int 0)
