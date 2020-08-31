open MyStdLib

module EvalContext = struct
  module Func = PairOf(Id)(Converter)
  module PTContext = DictOf(Id)(ParseTree)
  module FuncContext = DictOf(Id)(Func)

  type t =
    {
      pt_context : PTContext.t ;
      func_context : FuncContext.t ;
    }

  let empty : t =
    {
      pt_context = PTContext.empty ;
      func_context = FuncContext.empty ;
    }

  let insert_pt
      (ctx:t)
      (i:Id.t)
      (s:ParseTree.t)
    : t =
    { ctx with
      pt_context = PTContext.insert ctx.pt_context i s }

  let insert_pts
      (ctx:t)
      (ips:(Id.t * ParseTree.t) list)
    : t =
    List.fold
      ~f:(fun ptc (i,s) -> insert_pt ptc i s)
      ~init:ctx
      ips

  let lookup_pt
      (ctx:t)
      (i:Id.t)
    : ParseTree.t option =
    PTContext.lookup ctx.pt_context i

  let lookup_pt_exn
      (ctx:t)
      (i:Id.t)
    : ParseTree.t =
    PTContext.lookup_exn ctx.pt_context i

  let insert_func
      (ctx:t)
      (i:Id.t)
      (s:Func.t)
    : t =
    { ctx with
      func_context = FuncContext.insert ctx.func_context i s }

  let lookup_func
      (ctx:t)
      (i:Id.t)
    : Func.t option =
    FuncContext.lookup ctx.func_context i

  let lookup_func_exn
      (ctx:t)
      (i:Id.t)
    : Func.t =
    FuncContext.lookup_exn ctx.func_context i
end

let parse_tree_apply
    (pt:ParseTree.t)
    (c:Converter.t)
  : ParseTree.t =
  let rec apply
      (ctx:EvalContext.t)
      (c:Converter.t)
    : ParseTree.t =
    begin match c with
      | EmptyFunc -> failwith "shouldn't happen"
      | StringIntro s -> ParseTree.mk_terminal s
      | OrElim (i_old,i_new,c1,c2) ->
        let p = EvalContext.lookup_pt_exn ctx i_old in
        let (b,p) = ParseTree.destruct_or_exn p in
        let ctx = EvalContext.insert_pt ctx i_new p in
        if b then
          apply
            ctx
            c1
        else
          apply
            ctx
            c2
      | ConcatElim (i_old,i1,i2,c) ->
        let p = EvalContext.lookup_pt_exn ctx i_old in
        let (p1,p2) = ParseTree.destruct_concat_exn p in
        let ctx = EvalContext.insert_pts ctx [(i1,p1);(i2,p2)] in
        apply
          ctx
          c
      | OrIntro (b,c) ->
        ParseTree.mk_or
          b
          (apply
             ctx
             c)
      | ConcatIntro (c1,c2) ->
        ParseTree.mk_concat
          (apply ctx c1)
          (apply ctx c2)
      | Variable v -> EvalContext.lookup_pt_exn ctx v
      | Apply (fi,vi) ->
        let (i,c) = EvalContext.lookup_func_exn ctx fi in
        let pt = EvalContext.lookup_pt_exn ctx vi in
        let ctx = EvalContext.insert_pt ctx i pt in
        apply
          ctx
          c
      | Fix (fid,iarg,c) ->
        let ctx =
          EvalContext.insert_func
            ctx
            fid
            (iarg,c)
        in
        apply
          ctx
          c
    end
  in
  apply
    (EvalContext.insert_pt EvalContext.empty (Id.from_int 0) pt)
    c

let apply
    (g:Grammar.t)
    (s:string)
    (c:Converter.t)
  : string =
  let a = Automata.from_grammar g in
  let bs = Option.value_exn (Automata.parse a s) in
  let pt = ParseTree.from_bool_list g bs in
  let pt =
    parse_tree_apply
      pt
      c
  in
  ParseTree.to_string pt
