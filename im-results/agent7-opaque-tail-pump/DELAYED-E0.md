# D100 delayed E0 exposure: 53,257,978,073,992,275 steps

**Status:** exact macro proof and all 62 epochs compiled locally in Lean 4.36.0-rc2 against the verbatim reconstructed `Z0/run0/join0/sweepL/sweepR` model. Original-repository import closure and final WeightedBound bridge remain to be source-accepted. No global accepted count is changed here.

Literal `1RB1LA_1RC1LE_0RD1RF_0LD0LA_---0LB_1LD1RB`. This previously exceeded 300 million primitive steps without first-hole exposure. The actual first hole is E0 after 53,257,978,073,992,275 transitions; the E0=halt completion halts after one more step, and every other completion has no assigned halting instruction. The conservative weighted upper bound is 53,257,978,073,992,281.

## Exact recurrence

Use the original zipper convention, left list including the scanned cell, missing tape cells read zero. Let U(n)=1^n, Z(n)=0^n, V=1010, W=01. Define
- A(n,k,z) = (A, [], U(n) 0 U(k) Z(z)).
- B(j,R) = (B, [], 0 V^j R).

The blank prefix reaches A(1,0,2) after seven moves. The elementary right sweep takes B(j,R) to (C,0 U(4j+1),R) in 1+8j transitions. A six-step turn on 1111 gives B with a left unary block of length 4j+6; a two-step BE left sweep transfers each pair 11 to 01. Therefore B(j,1111R) -> B(j+1,1R) at cost 12j+13. Iteration yields the closed cost 12ja+6a²+7a for a applications from j.

For n=3j+r with r=1,2,3, the scan phase costs 6j²+15j+4 and leaves (C,0 U(4j+1),1^r 0 1^k 0^z). The finite boundary turn (at most 15 steps on this trace) is a literal arbitrary-tail identity, so no giant unary tape is evaluated. If its output is (A,1^p L,0 1^k' 0^z') for input (C,0 L,1^r 0 1^k 0^z), an A sweep gives A(4j+1+p,k',z') in a further 4j+1+p moves.

At epoch 61, time 29,957,612,701,154,721, the configuration is A(186950655,3,2). Here j=62316884, r=3. The terminal nine-step turn leaves B with an odd unary block of length 4j+9=249267545. Paired BE sweeps remove 249267544 cells; B1 then moves left into E with empty left list (hence scanned zero). The exact right list is 1 (01)^124633772 00. This proves the exposure, rather than just extrapolating a growth pattern.

## Artifacts

- [D100Delayed.lean](D100Delayed.lean): arbitrary-tail transition identities and inductive sweeps.
- [D100DelayedTrace.lean](D100DelayedTrace.lean): 61 ordinary epochs and final odd terminal epoch, each boundary turn proved by `rfl`, chained by `join0`. Local `reached` axiom profile: [propext, Quot.sound]; `hole`: [propext]. No sorry, native_decide or evaluated multi-million-cell lists.
- [D100DelayedBound.lean](D100DelayedBound.lean): proposed original-source `zipRead` / `WeightedBound` wrapper, using existing Run0ExposureBound and FastZipWeight. Source acceptance still required.

The two locally compiled files had Git blob IDs eb35dcc39003d1b609e2414153a2f4bc728fcfd3 and 1e87b2456cbf3a20055fe4ead188e4f18c14a77a respectively. The precise result to incorporate after source CI is a finite first-hole upper bound, not a never-halting certificate. This leaf is far below the champion threshold.
