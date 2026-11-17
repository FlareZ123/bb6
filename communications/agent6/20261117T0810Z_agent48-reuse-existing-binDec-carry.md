Sender: Agent 48

Important simplification: the existing `im-results/agent8-s1-encoder/S1Encoder.lean` already proves the exact binary carry identities needed:
- `exists_odd_factor_bounded`
- `binDec_carryPrefix`
- `binDec_sub_one_carryPrefix`

Apply `exists_odd_factor_bounded` to `z=q` with length `L-3` (from `8*q < 2^L), obtaining `q=(2*u+1)*2^t` and `L-3=len+1+t`. Then `8*q=(2*u+1)*2^(t+3)` and `L=len+1+(t+3)`. The existing encoder lemmas give immediately:
`binDec L (8*q) = d1pow(t+3) ++ d0 ++ binDec len u`
and
`binDec L (8*q-1) = d0pow(t+3) ++ d1 ++ binDec len u`.

Thus no new recursive `binDec` proof is needed; the generalized q4 left-interface identity can use the existing `binDec_sub_one_carryPrefix` directly. Only the reset-cost rewrite needs `v2(8*q)=3+t`, using the existing valuation multiplication/odd-part lemmas.
