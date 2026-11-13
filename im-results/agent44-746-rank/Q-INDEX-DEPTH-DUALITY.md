# Q-index / Q-depth selector duality

**Status: exact corollary of two selector drafts; integration Lean proof not yet compiled.** Keep in `im-results/`. This is an arithmetic description of the #746 t=1 candidate locus, not a blank-root exclusion.

## Common numerator

Agent 44's index-coordinate module defines
[
Q^{I}_j(n)=28\cdot2^n-2n+15-2^{j+4}(2n+3)
]
and proves `qNumerator_eq_signedZ`, i.e.
[
Q^{I}_j(n)=8\,\operatorname{signedZ}(n,j)-9(2^{n+2}+2n+1).
]
Agent 7's depth-coordinate module defines exactly the right-hand side as (Q^{D}_j(n)). Thus the two Lean definitions are propositionally equal by one rewrite; there is no extra number-theoretic hypothesis.

## Duality theorem

For (s\in\{4,5\}), (j) even, and (k,h\ge0), the two existing selector iff theorems give
[
3^{k+1}\mid Q_j(s+6h)
\iff h\bmod3^k=\operatorname{qIndexResidue}(s,j,k)
\iff j\bmod(2\cdot3^k)=\operatorname{qDepthResidue}(s+6h,k).
]
The only bridge needed is the equality of the two `qNumerator` definitions. In Lean, after importing `QStateIndexHensel` and `QDepthSelector`, the core integration theorem is:

```lean
theorem qNumerators_agree (n j : Nat) :
    CascadeQStateIndexHensel.qNumerator n j =
      CascadeQDepthHensel.qNumerator n j := by
  rw [CascadeQStateIndexHensel.qNumerator_eq_signedZ]
  rfl

theorem qIndexDepth_duality (s j k h : Nat)
    (hs : s=4 ∨ s=5) (hj : j%2=0) :
    h%3^k = CascadeQStateIndexHensel.qIndexResidue s j k ↔
      j%CascadeRayDepthHensel.depthPeriod k =
        CascadeQDepthHensel.qDepthResidue (s+6*h) k := by
  have hn : (s+6*h)%6=4 ∨ (s+6*h)%6=5 := by
    rcases hs with hs|hs <;> omega
  have hi := CascadeQStateIndexHensel.qIndexResidue_iff s j k h hs hj
  have hd := CascadeQDepthHensel.qDepthResidue_iff (s+6*h) k j hn
  have hsame :
      CascadeQStateIndexHensel.qNumerator (s+6*h) j =
        CascadeQDepthHensel.qNumerator (s+6*h) j :=
    qNumerators_agree (s+6*h) j
  have hi' :
      (3:Int)^(k+1) ∣
          CascadeQDepthHensel.qNumerator (s+6*h) j ↔
        h%3^k = CascadeQStateIndexHensel.qIndexResidue s j k := by
    simpa only [hsame] using hi
  exact hi'.symm.trans hd
```

The two selectors are therefore mutual inverses at each finite precision. The first inverse identity follows by setting (h=\operatorname{qIndexResidue}(s,j,k)) and using `qIndexResidue_lt`. The second follows by setting (j=\operatorname{qDepthResidue}(s+6h,k)), using `qDepthResidue_good` to obtain (3\mid Q_j(n)), then `q_mod_three_even_iff` to prove that selected depth is even, and applying the duality theorem plus `qDepthResidue_lt`.

Consequently, for each sector (s=4,5) and precision (k), the admissible (h\bmod3^k) classes and even (j\bmod(2\cdot3^k)) classes are in canonical bijection. Each coordinate selects exactly one partner in the other coordinate.

## Stronger consequence: finite-level 3-adic isometry

For each fixed sector (s=4) or (5), the depth selector is not merely a pointwise inverse table. It is an isometry of finite 3-adic coordinate spaces. The selector output is always even, because (qDepthResidue_good) gives (3\mid Q) and (q_mod_three_even_iff) forces even depth; it is also canonical in (0\le j<2\cdot3^k). Therefore (x_k(h)=qDepthResidue(s+6h,k)/2) is a well-defined residue in (mathbb Z/3^k).

The duality theorem gives the exact equivalence
[
qDepthResidue(s+6h_1,k)=qDepthResidue(s+6h_2,k)
\iff h_1\equiv h_2\pmod{3^k}.
]
- Forward: take the common selected even depth (j). Applying the duality theorem to both (h_1) and (h_2) identifies both index residues with the same (qIndexResidue(s,j,k)).
- Reverse: take (j=qDepthResidue(s+6h_2,k)), use its canonical representative and the duality theorem to identify (h_2\bmod3^k) with (qIndexResidue(s,j,k)). The assumed congruence gives the same index for (h_1); applying duality again forces (j=qDepthResidue(s+6h_1,k)).

Thus (h\bmod3^k\mapsto qDepthResidue(s+6h,k)/2\bmod3^k) is a bijective isometry, with inverse given by the index selector. Compatibility of the recursive selectors across precisions then identifies the inverse-limit zero locus with the graph of a 3-adic isometry between the fatal-index coordinate and the half-depth coordinate. This is a structural corollary, not a root exclusion; it is conditional on the Q-state selector's eventual source-CI verification.

## Nested odd-parent exponent is a single index cylinder

The source-coordinate identity in `qNumerator_t1_parent_identity` is
[
Q_j(n)=9(2q+5)
]
for the actual parent (q) of the ray state under the t=1 odd arm. It therefore shifts the 3-adic valuation by exactly two:
[
3^{t+3}\mid Q_j(n)
\iff 3^{t+1}\mid(2q+5).
]
Combining this with `qIndexResidue_iff` at precision (k=t+2) gives
[
3^{t+1}\mid(2q+5)
\iff h\bmod3^{t+2}
 =qIndexResidue(s,j,t+2),
\qquad n=s+6h.
]
So, conditional on the explicit source t=1 parent equations, a further odd parent with exponent at least (t) is supported on exactly one index residue class modulo (3^{t+2}). Exact exponent (t) is obtained by removing the unique next-level lift at precision (t+3); the other two lifts of the lower cylinder have exact valuation (v_3(2q+5)=t+1).

The short Lean bridge to add after the source identity is:

```lean
theorem qNumerator_t1_divisibility (n j q t : Nat)
    (hQ : qNumerator n j = 9*(2*q+5)) :
    (3:Int)^(t+3) ∣ qNumerator n j ↔
      (3:Int)^(t+1) ∣ (2*q+5) := by
  rw [hQ]
  have hpow : (3:Int)^(t+3)=9*(3:Int)^(t+1) := by
    rw [show t+3=(t+1)+2 by omega, Int.pow_add]
    norm_num
  rw [hpow]
  exact Int.mul_dvd_mul_iff_left (by norm_num : (9:Int)≠0)
```

Composing this with `qIndexResidue_iff` at (t+2) gives the unique index cylinder. This makes the generic Q-index selector directly reusable for the next odd-parent layer, rather than only for the first U/Q numerator. The statement is conditional on the source t=1 hypotheses and the unverified Q-state Lean module; it does not assert that every such cylinder satisfies the dyadic image band.

## Nested odd-parent exponent is a single index cylinder

The source-coordinate identity in `qNumerator_t1_parent_identity` is
[
Q_j(n)=9(2q+5)
]
for the actual parent (q) of the ray state under the t=1 odd arm. It therefore shifts the 3-adic valuation by exactly two:
[
3^{t+3}\mid Q_j(n)
\iff 3^{t+1}\mid(2q+5).
]
Combining this with `qIndexResidue_iff` at precision (k=t+2) gives
[
3^{t+1}\mid(2q+5)
\iff h\bmod3^{t+2}
 =qIndexResidue(s,j,t+2),
\qquad n=s+6h.
]
So, conditional on the explicit source t=1 parent equations, a further odd parent with exponent at least (t) is supported on exactly one index residue class modulo (3^{t+2}). Exact exponent (t) is obtained by removing the unique next-level lift at precision (t+3); the other two lifts of the lower cylinder have exact valuation (v_3(2q+5)=t+1).

The short Lean bridge to add after the source identity is:

```lean
theorem qNumerator_t1_divisibility (n j q t : Nat)
    (hQ : qNumerator n j = 9*(2*q+5)) :
    (3:Int)^(t+3) ∣ qNumerator n j ↔
      (3:Int)^(t+1) ∣ (2*q+5) := by
  rw [hQ]
  have hpow : (3:Int)^(t+3)=9*(3:Int)^(t+1) := by
    rw [show t+3=(t+1)+2 by omega, Int.pow_add]
    norm_num
  rw [hpow]
  exact Int.mul_dvd_mul_iff_left (by norm_num : (9:Int)≠0)
```

Composing this with `qIndexResidue_iff` at (t+2) gives the unique index cylinder. This makes the generic Q-index selector directly reusable for the next odd-parent layer, rather than only for the first U/Q numerator. The statement is conditional on the source t=1 hypotheses and the unverified Q-state Lean module; it does not assert that every such cylinder satisfies the dyadic image band.

## Verification boundary

- Agent 7's `QDepthDefs`, `QDepthLift`, `QDepthSelectorBase`, `QDepthSelector`, and `QDepth887` all compiled in original-source workflow run [43397274339](https://github.com/FlareZ123/bb6/actions/runs/43397274339), at head `4a8ee37bd33aab1a63d327f612d1fb89baafe781`. The log printed `qDepthResidue_iff`, `qDepthResidue_unique_in_period`, and `qDepthResidue_887_table` with axiom profile `[propext, Classical.choice, Quot.sound]`; the workflow later failed in the unrelated `UParentCone887.lean:75` application.
- Agent 44's `QStateIndexHensel.lean` remains uncompiled by original-source CI. Its BigInt specialization is corroboration only.
- The duality and inverse-selector integration above is a proof sketch, not a compiled theorem.
- The t=1 source identity (Q_j(n)=9(2q+5)) is conditional on the explicit signed-coordinate and parent-equation hypotheses in `qNumerator_t1_parent_identity`. Neither selector proves that the authentic blank orbit reaches or avoids a corresponding parent.

## Immediate integration note

The failure in run 43397274339 is downstream of the Q-depth modules, at `UParentCone887.lean:75`. Given the source constructor's bundled band premise, replace
`Or.inr ⟨k,t,d,hdodd,hband.1,hband.2,hout,hscale⟩`
with
`Or.inr ⟨k,t,d,hdodd,hband,hout,hscale⟩`.
This is a local constructor-shape correction; it does not alter the mathematical claim.
