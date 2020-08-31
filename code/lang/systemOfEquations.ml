open MyStdLib
open Lacaml.S

module IdMap = DictOf(Id)(FloatModule)

type t = IdMap.t * Float.t
[@@deriving eq, hash, ord, show]

let mk_constant
    (x:Float.t)
  : t =
  (IdMap.empty,x)

let zero : t = mk_constant 0.

let mk_variable
    (i:Id.t)
  : t =
  (IdMap.singleton i 1.,0.)

let scale
    ((m,f):t)
    (f':Float.t)
  : t =
  (IdMap.map_values ~f:(( *. ) f') m, f *. f')

let sum
    ((m1,f1):t)
    ((m2,f2):t)
  : t =
  (IdMap.merge_to_dict
     ~combiner:(+.)
     m1
     m2
  ,f1 +. f2)

module IntMap = DictOf(IntModule)(Id)
module IdSet = SetOf(Id)

let to_matrix
    (im:IdMap.t)
    (iim:IdMap.t list)
  : Mat.t =
  failwith "ah"

let solve
    (ss:t list)
  : (Id.t * Float.t) list =
  let row_count = List.length ss in
  let ids =
    List.fold
      ~f:(fun ids (m,_) ->
          List.fold
            ~f:(fun ids i ->
                if IdSet.member ids i then
                  ids
                else
                  IdSet.insert i ids)
            ~init:ids
            (IdMap.key_list m))
      ~init:IdSet.empty
      ss
  in
  let col_count = IdSet.size ids in
  let im =
    fst
      (List.fold
         ~f:(fun (im,n) i ->
             (IntMap.insert im n i,n+1))
         ~init:(IntMap.empty,0)
         (IdSet.as_list ids))
  in
  let lookup
      (i:int)
      (j:int)
    : Float.t =
    let i = i - 1 in
    let j = j - 1 in
    let (m,_) = List.nth_exn ss i in
    let id = IntMap.lookup_exn im j in
    IdMap.lookup_default
      ~default:Float.zero
      m
      id
  in
  let mx =
    Mat.init_rows
      row_count
      col_count
      lookup
  in
  let ans =
    Mat.init_rows
      row_count
      1
      (fun r _ ->
         let r = r - 1 in
         Float.neg (snd (List.nth_exn ss r)))
  in
  gesv
    mx
    ans;
  let ans =
    Vec.to_list @$
    Mat.col
      ans
      1
  in
  IdMap.as_kvp_list
    (List.foldi
       ~f:(fun i m f ->
           IdMap.insert
             m
             (IntMap.lookup_exn im i)
             f)
       ~init:IdMap.empty
       ans)

let neg
    (x:t)
  : t =
  scale
    x
    (-1.0)
