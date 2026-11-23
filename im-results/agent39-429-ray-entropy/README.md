# BB429: square-root sparsity of the branch-10 q0 candidate parameters

**Mathematical status:** exact paper proof from the original repository accelerator's exhaustive high-output inverse equations, with the reusable inverse-word congruence and phase lemmas locally Lean-compiled (4.36.0-rc2, standard `[propext, Quot.sound]` only). The complete original-source reachability/counting wrapper has **not yet passed its transitive Lean import**, so do not describe the final quantified cardinality bound as source-certified. This is an intermediate restriction, **not** a blank-machine decision, an upper bound on BB(6), or a new halting witness.

## Main result: a square-root, not merely modular, sieve

Let `next`, `run` and the genuine blank section root `(0,0)` be the exact `BB429` definitions of [Agent 5's authenticated accelerator](../agent5-429-rank/BB429Rank.lean), with source inverse lemmas [`BB429NewResidue.odd_inverse/even_inverse`](../agent6-harmonic429/BB429NewResidue.lean). Define
`Reach(a,b) := ∃ t, BB429.run t (0,0) = some (a,b)`.
The open branch-10 q0 feeder has the specific source-derived parametrization
\[
 n(u)=23+32u,\qquad A(u)=13\cdot2^{n(u)}-24u-19,\qquad B(u)=2A(u)-13,
 \quad u\ge0.
\]
See [the existing q0 derivation](../agent1-429-q0-23-7/Q0ResidueCoverage.md). Let `U = {u ∈ ℕ : Reach(A(u),B(u))}`.

**Theorem (paper, quantitative).** For every integer `X ≥ 2`, putting `k=⌈log₂ X⌉+3`,
\[
 \#\{u<X:u\in U\}\;\le\; k+2^{\lfloor k/2\rfloor}
 \;<\; \log_2 X+4+4\sqrt X.
\]
In particular `#(U∩[0,X))=O(√X)`, hence **the surviving q0 candidate parameter set has zero natural density**. This is a restriction on candidate *parameters*, not a proportion of six-state machines, an authentic run-time bound, or a proof that any candidate is reachable.

## Proof: every second inverse letter is forced

Set `R(a,b)=2a+b`. For every high-output target `a≥13`, the complete source inverse equations allow only:

| label | predecessor `(x,y)` | rank decrease |
| --- | --- | ---: |
| F | `a=2x+3, y=b+a` | 3 |
| S | `4x+26=4a+b, 2y=b+4` (odd `a`, `b≡2 mod4`) | 11 |
| E | `4x+14=4a+b, 2y=b` (even `a`, `b≡2 mod4`) | 7 |

Each inverse rank cost is `3 mod4`. For a target on the ray `b=2a-13`, its initial rank is `4a-13≡3 mod4`. Therefore after `j` inverse steps, independently of the choices, `R_j≡3+j (mod4)`. If `j` is even, `R_j` and `b_j` are odd, so only F is possible. At `j≡1 mod4`, `R_j≡0`, so the only candidate labels are F/S (E would force both even `a_j` and `b_j≡2 mod4`, incompatible with rank 0). At `j≡3 mod4` the options are F/E. Hence all length-`k` inverse words belong to the regular language
```
F (F|S) F (F|E) F (F|S) F (F|E) ...
```
and there are at most `2^⌊k/2⌋` words.

For a fixed word `w`, write `a_j=(C_j a_0+D_j)/2^j` for its `j`-th predecessor first coordinate. Initially `C_0=1,D_0=0`. On F, `C_{j+1}=C_j`; on S or E, since `R_j=4a_0-13-δ_j` with `δ_j` the accumulated rank costs,
`a_{j+1}=a_j/2+a_0-(13+δ_j+c_w)/4`
where `c_w=26` (S) or 14 (E). Thus `C_{j+1}=C_j+2^{j+1}` on S/E. For these steps `j` is odd and `13+δ_j+c_w` is even, so all constants `D_j` are integers. **Every `C_j` is odd.** Since `a_k` is an integer, `2^k | (C_k a_0+D_k)`; an odd `C_k` is invertible modulo `2^k`. Consequently **one fixed inverse word admits at most one initial `a_0` residue modulo `2^k`**.

The same fact has an alternative coefficient-free proof: two inverse histories carrying the same word, from targets with the same ray offset, have
`2^j(a_j-a'_j)=C_j(a_0-a'_0)` with odd `C_j`. The F step preserves `C_j`; S/E adds `2^{j+1}`. Thus `a_0≡a'_0 mod2^k`. This quantified uniqueness, the exact branch costs, and the mod-four phase restrictions are checked in [the Lean arithmetic core](BB429InverseWordCore.lean); the core does not silently assume that every syntactic inverse word occurs on the blank orbit.

## Unbounded high-counter prefix and the q0 count

Any legitimate predecessor of a target with `a≥13` satisfies `a≤2x+3`, so `a+3≤2(x+3)`. If `a_0+3≥16·2^k` and the target is blank-reachable, following its actual rooted predecessors for `k` steps keeps every first counter at least 13 (the genuine root has first counter zero). Thus its first `k` inverse labels are governed by the exhaustive high-output grammar above. For each fixed `k`, all sufficiently large reachable points on `b=2a−13` lie in at most `2^⌊k/2⌋` residue classes modulo `2^k`, giving zero natural density for the ray itself.

For `u≥k`, the elementary inequality `24u+19≤2^{23+32u}` implies `A(u)≥12·2^{23+32u}≥24·2^k`. Thus every `u≥k` in `U` admits a length-`k` inverse word. Since `n(u)≥k`, `A(u)≡−24u−19 mod2^k`. Two such parameters with the same word therefore obey `2^k | 24(u-v)`; since `24=8·3` with `3` odd, `u≡v mod2^{k-3}`. For `k=⌈log₂X⌉+3`, `2^{k-3}≥X`, hence **at most one** `u∈[k,X)` per word. There are fewer than `k` exceptional small parameters, yielding the asserted bound. No infinite trajectory simulation or finite-sample-to-universal extrapolation is involved.

## Evidence boundary and next decisive use

The three inverse equations and root `run` are imported source facts from the linked modules; the arithmetic core is a locally successful **abstract exact-grammar** Lean proof, not an original-source import. Complete source certification requires an exact `BB429.next`→legitimate-edge bridge, an induction constructing each high-counter rooted prefix, and a counting theorem (or a carefully scoped mathematical proof of the latter). These are precisely separated to avoid confusing a synthetic inverse ray with actual blank reachability.

The quantitative sparsity still allows infinitely many exceptional parameters and cannot close branch-10 q0, the competing inverse branches, #429, or BB(6). A consequential next question is whether the surviving dyadic inverse language intersects the very special exponential-affine q0 ray at **any** parameter, not how many low-modulus residues can be filtered.

