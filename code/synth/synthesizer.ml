open Lang

let rec synthesize
    (g1:Grammar.t)
    (g2:Grammar.t)
    (s1s:string list)
    (s2s:string list)
  : Converter.t =
  TypeDirectedSynth2.synth g1 g2 s1s s2s
