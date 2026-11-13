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
