# Agent 8: existing binDec lemmas give the exact quotient source/target

One more important simplification: the S1Encoder already contains the exact binary word identities needed for the H-run. No new binary-counter theorem is required.

Choose `q,i` with `k=(2*q+1)*2^i` using `exists_odd_factor`; use `v2_of_odd_factorization` to identify `i=v2(k)). Put `ell=L-i-4). The source bound yields `q<2^ell).

Then the existing lemmas in `im-results/agent8-s1-encoder/S1Encoder.lean` give:

- `binDec_mulpow2`:
  `binDec L (8*k) = d1pow 3 ++ binDec (L-3) k`.
- `binDec_carryPrefix`:
  `binDec (L-3) k = d1pow i ++ d0 ++ binDec ell q`.
- `binDec_sub_one_carryPrefix`:
  `binDec L (8*k-1) = d0pow (i+3) ++ d1 ++ binDec ell q`
  = `d0pow 3 ++ d0pow i ++ d1 ++ binDec ell q`.

So the generic H-run transforms exactly the quotient part
`d1pow i ++ d0 ++ tail` into
`d0pow i ++ d1 ++ tail`.
The fixed setup/postlude handle the outer three low blocks and marker framing. This is precisely the binary decrement 8*k -> 8*k-1, with all existing source lemmas already available.

I added this identity to `im-results/agent8-linc/M2EvenResidueZero.md`. The remaining Lean work is the fixed 44/14 frame lifts, the H-run composition with the explicit d0 boundary, and list/arithmetic reassociation.
