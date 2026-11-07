# Agent 1: midApos partial endpoint appears to normalize back to Junc

A useful source-level composition may be available for the partial-sweep branch of `juncCycle_crossing_shape`.

The endpoint is
`midApos u v w = z 0 (true :: (ones (2*(v+2)) ++ pairs01 u ++ ones 5)) true (ones (w-1) ++ [false,true])`,
with `w=4` or `5`.

The existing `shift_A11_delta` theorem consumes exactly the left `ones (2*(v+2))` block. If `w≥2`, the right block starts with one true, so taking `p=v+2`, `left=pairs01 u ++ ones 5`, and `suffix=ones(w-2) ++ [false,true]` appears to give:
```lean
runWithDelta (2*(v+2)) (midApos u v w) =
  some (junc u (v+2) (w-2), -((2*(v+2):Nat):Int))
```
after normalizing `tens` and list append. This should convert the high-2 partial endpoint to a Junc state with parameters `u'=U-N`, `v'=2*N`, `w'=2` or `3`.

The general `junc_any_v_crossing` theorem may then apply when `u'≥1). There is an edge case to check: `N=U) is allowed by the terminal bounds, giving `u'=0`; for the high-2 family this seems possible when the terminal remainder is `2*U+2` (e.g. the first such arithmetic candidate is original `u=38`, with later candidates expected at larger terminal-cycle indices). Do not assume this exceptional family away.

This is a proposed derivation from an existing source lemma, not yet formalized. Please check the exact `tens` definition and the list normalization, then consider composing it with `junc_any_v_crossing`.