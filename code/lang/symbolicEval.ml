open MyStdLib

module Context =  DictOf(Id)(Converter)

let extract_unsatisfied
    (c:Converter.t)
    (pts:ParseTree.t list)
  : ParseTree.t list =
  let rec extract_unsatisifed
      (ctx:Context.t)
      (c:Converter.t)
      (ptbs:(ParseTree.t * bool * bool) list)
    : (ParseTree.t * bool) list =
    let extract_unsatisifed_simple = extract_unsatisifed ctx in
    if List.for_all ~f:(not % snd3) ptbs then List.map ~f:(fun (pt,b,_) -> (pt,b)) ptbs else
    begin match c with
      | EmptyFunc -> List.map ~f:(fun (pt,_,_) -> (pt,false)) ptbs
      | StringIntro _ -> List.map ~f:(fun (pt,b,_) -> (pt,b)) ptbs
      | Variable _ -> List.map ~f:(fun (pt,b,_) -> (pt,b)) ptbs
      | OrElim (_,_,c1,c2) ->
        let ptbs1 = extract_unsatisifed_simple c1 ptbs in
        let ptbs2 = extract_unsatisifed_simple c2 ptbs in
        List.map2_exn
          ~f:(fun (pt,b1) (_,b2) -> (pt,b1 || b2))
          ptbs1
          ptbs2
      | ConcatElim (_,_,_,c) ->
        extract_unsatisifed_simple c ptbs
      | OrIntro (b,c) ->
        let ptbs_oldpts =
          List.map
            ~f:(fun (pt,bold,_) ->
                if bold then
                  let (b',pt') = ParseTree.destruct_or_exn pt in
                  ((pt',(b = b'),true),pt)
                else
                  ((pt,bold,false),pt))
            ptbs
        in
        let (ptbs,oldpts) =
          List.unzip
            ptbs_oldpts
        in
        let ptbs =
          extract_unsatisifed_simple
            c
            ptbs
        in
        List.map2_exn
          ~f:(fun (_,b) pt -> (pt,b))
          ptbs
          oldpts
      | ConcatIntro (c1,c2) ->
        let ptbs_left_right_old =
          List.map
            ~f:(fun (pt,b,_) ->
                if b then
                  let (pt1,pt2) = ParseTree.destruct_concat_exn pt in
                  ((pt1,b,true),(pt2,b,true),pt)
                else
                  ((pt,b,false),(pt,b,false),pt))
            ptbs
        in
        let (ptbs1,ptbs2,pt_olds) =
          List.unzip3
            ptbs_left_right_old
        in
        let ptbs1 =
          extract_unsatisifed_simple
            c1
            ptbs1
        in
        let ptbs2 =
          extract_unsatisifed_simple
            c2
            ptbs2
        in
        List.map3_exn
          ~f:(fun (_,b1) (_,b2) pt ->
              (pt,b1 && b2))
          ptbs1
          ptbs2
          pt_olds
      | Apply (f,_) ->
        let c = Context.lookup_exn ctx f in
        let ptbs =
          List.map
            ~f:(fun (pt,b,prog) -> (pt,b && prog,false))
            ptbs
        in
        extract_unsatisifed_simple
          c
          ptbs
      | Fix (i,_,c) ->
        let ctx = Context.insert ctx i c in
        extract_unsatisifed
          ctx
          c
          ptbs
    end
  in
  let ptbs =
    extract_unsatisifed
      Context.empty
      c
      (List.map ~f:(fun pt -> (pt,true,true)) pts)
  in
  List.filter_map
    ~f:(fun (pt,b) -> if b then None else Some pt)
    ptbs

let covers_all_examples
    (c:Converter.t)
    (pts:ParseTree.t list)
  : bool =
  List.is_empty (extract_unsatisfied c pts)
