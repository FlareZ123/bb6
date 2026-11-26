# E0=0RF normalized Raw139 candidate partition (one exception)

Parent codes `[7,24,11,24,14,24,24,16,21,11,24,24]`. The deterministic reproduction script uses a 250-step translated-cycle/small-FAR split search followed by block-FAR and late-query search. Initial 29,610 splits, 681,031 ordinary leaves: 505,223 translated cycles, 115,143 last-hole finite queries, 55,394 FAR, 5,271 open. Extended search resolves 5,215 open by block-FAR, 50 by finite queries, four by cycles. All 50 late finite queries are single-hole leaves; largest query is 2037. Candidate weighted bound 2043 for the nonexceptional leaves.

## Exact proof of residual 4570

Table `[7,9,11,21,14,23,24,16,21,11,3,20]` (D0 unassigned). `PadGrowth.lean` establishes exact tape-equivalence transport for blank padding, and `ZeroRF4570.lean` proves six phases of a growth recurrence. In F0 with a blank left half, a right run of even length n >= 6 maps to length n+24 in 30n+1020 primitive steps, up to far-end blank padding. Authentic seed at step 967 has n=24. Local Lean 4.36.0-rc2 accepts period, growth, never (propext, Quot.sound); exact `Hybrid` transport to its weighted Cover also passes (standard axioms). Sources used the dependency oleans from CI zeroRC core artifact 15121390168. Independent source-connected parent verification is not yet done.

## Remaining exception 1892

Table `[7,24,11,17,14,8,3,16,21,11,12,13]`, A1 unassigned. `ZeroRF1892Macros.lean` proves seven A0 section rules exactly with arbitrary tails, including long transfers. L and R nearest-first excluding the scanned 0. A0 maps:
- L=1^x 0 U, R=00 T -> L'=1 U, R'=1^(x+2) T, cost 3x+10.
- L=1^x 0 1^y 0 U, y>=1, R=01 T -> L'=1 U, R'=1^y 0^(x+3) T, cost x+3y+7.
- R=110 T -> L'=11 L, R'=1 T, cost 8.
- L=1^x 0 U, R=111 T -> L'=1 U, R'=1^(x+1) 00 T, cost 3x+10.
- R=100 T -> L'=101 L, R'=T, cost 5.
- R=1011 T -> L'=1001 L, R'=T, cost 8.
- R=10100 T -> L'=10001 L, R'=T, cost 5.

Failure prefixes include R=10101 and R=01 without required second left run. No unbounded proof for this machine yet: observed left one-run parity and gap constraints do not form an inductive invariant. Equal/asymmetric ngram, run-grammar, block-FAR, bounded prefix abstraction and backward prefix preimage search did not close. A proof of the exception would finish the candidate classification; full exact Cover assembly still needs audit. No parent closure is claimed.

Run `python reproduce.py` to regenerate partition and recipes (requires repository source and g++). Recipes are candidate data, not proof artifacts.
