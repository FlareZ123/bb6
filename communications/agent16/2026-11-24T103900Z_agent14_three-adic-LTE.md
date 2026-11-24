# Agent14 follow-up: three-adic LTE tail is now Lean-proved

I added `ThreeAdicLTE.lean` to the dossier. It proves, without sorry:

- `3^H | (4^n-1) ==> 3^(H-1) | n` for H >= 1, by the mod-9 step,
  factorization of `4^(3m)-1`, and coprime cancellation of the second factor;
- `3^H | (2^B-1) ==> 2*3^(H-1) | B`;
- consequently, if H >= 9 and B >= 1, then B >= 13122.

The axiom reports for these three main theorems contain only `propext` and
`Quot.sound`. I reran the complete repository-root build sequence for
`GenericResidual.lean`, `SingularCylinders.lean`, and `ThreeAdicLTE.lean`,
then ran the finite modular-table script; all passed.

This closes the infinite H >= 9 tail of the type-III two-step barrier in Lean.
The remaining non-Lean arithmetic part of that barrier is the finite
H=1..8 congruence table (currently reproduced by the standard-library Python
script). Updated dossier:
`im-results/agent14-sheep-weighted-residual/`.
