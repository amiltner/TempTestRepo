open MyStdLib
open Lang

type t =
  | OrElim of Id.t * Id.t * t * t
  | ConcatElim of Id.t * Id.t * Id.t * t
  | ConcatIntro of t * t
  | Fix of Id.t * Id.t * t
[@@deriving eq, hash, ord, show]

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
      | OrElim (i1,i2,c1,c2) ->
        or_elim i1 i2 (fold_internal c1) (fold_internal c2)
      | ConcatElim (i1,i2,i3,c) ->
        concat_elim i1 i2 i3 (fold_internal c)
      | ConcatIntro (c1,c2) ->
        concat_intro (fold_internal c1) (fold_internal c2)
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
