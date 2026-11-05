# #746: a genuine-root dead branch in two uniform fatal-index classes

**Agent 10, 2026-11-05.** Intermediate root-sensitive theorem for the six-state machine
`1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA`.
The original machine's blank-tape halting verdict, and the exact value BB(6), remain open.

## Exact claim

Let $P=2^n$, $F_n=4P-n-4$, and $n\ge13$ with
$n\bmod54\in\{35,46\}$. The previous source-certified [FourthExactTwo.lean](FourthExactTwo.lean)
proves that actual blank-root reset reachability of $F_n$ is equivalent to
reachability of either of two immediate parents of
$u_4=4P-31n-49$:

- even branch $e_n=4P-63n-97$;
- odd branch $v_n=(14P-257n-399)/9$, exactly the source expression `oddPre n`.

**New theorem:** the entire odd branch is unreachable from the genuine
post-initial source-C root $(2,0)$, for every such index, with no finite
cutoff. Thus the surviving gate reduces to one parent:

```lean
theorem odd_fork_branch_unreachable (n : Nat) (hn : 13 ≤ n)
    (hres : n%54=35 ∨ n%54=46) :
    ¬CascadeSweep.ReachC (2,0) (oddPre n,0)

theorem fatal_iff_even_fifth_parent (n : Nat) (hn : 13 ≤ n)
    (hres : n%54=35 ∨ n%54=46) :
    CascadeSweep.ReachC (2,0) (fatal n,0) ↔
      CascadeSweep.ReachC (2,0) (evenPre n,0)
```

Source file: [ForkOddDead.lean](ForkOddDead.lean).

## Proof mechanism

In these index classes the odd target has exact linear identity
$9v_n+257n+399=14P$ and residue $v_n\bmod3=1$.
The antecedent source-C result
`CascadeAncestry.reachable_even_reset_parent` forces any genuine
predecessor of a reachable reset with this residue into an *even*
source-image band. Here $v_n$ occupies the unique even band at
$k=n-2$. The only possible earlier reset is therefore

$
w_n = 2v_n-2P-(n-2)
    = (10P-523n-780)/9.
$

An elementary induction proves $P\ge523n+781$ for all $n\ge13$.
Consequently $P<w_n<(3/2)P-1$ and $w_n\bmod3=1$.
Every even-image band is disjoint from this dyadic gap: scales
$k\le n-3$ end below $P$, while scales $k\ge n-2$
start at or above $(3/2)P-1$.
The previously source-proved `CascadeSweep.root_excludes_nonimage`
therefore excludes $w_n$ from the *entire* genuine blank-derived
source-C orbit. Reachability of $v_n$ would imply reachability of
$w_n$, a contradiction. The last theorem composes the exclusion with
`CascadeAgent10ExactlyTwo.genuine_fatal_iff_two_parent_roots`.

The proof uses the existing full source first-reset grammar, true
blank-root `ReachC` semantics, and no finite enumeration assumption.
It does **not** prove that the remaining even parent is unreachable.
No conclusion is drawn about the other surviving $n\bmod54$ classes.

## Validation and provenance

The new file compiled locally in Lean **4.36.0-rc2**, with no
`sorry` or `native_decide`, against a minimal signature stub for
the unchanged source theorems `odd_factor`, `odd_band`,
`reachable_even_reset_parent`, `even_band_unique`,
`root_excludes_nonimage` and
`genuine_fatal_iff_two_parent_roots`. The local axiom report includes
these *explicit stub declarations*, so the staging check is **not**
a full original-source proof.

The existing manual source workflow
[agent7-746-uniform-fatal-parent.yml](../../.github/workflows/agent7-746-uniform-fatal-parent.yml)
has been extended to compile `ForkOddDead.lean` after its full
unchanged dependencies. Its dispatch on 2026-11-05 is
[run 42065041818](https://github.com/FlareZ123/bb6/actions/runs/42065041818).
**Check the run conclusion and axiom lines before reporting an
unchanged-source certificate.** If it fails, repair the specific
integration issue rather than treating that as a refutation.

The local independent exact integer inverse routine
[reset_inverse_fast.py](reset_inverse_fast.py) reproduces the parent
relations at concrete examples and selected indices up to 500.
Those samples are only diagnostics; the quantified Lean proof is the
mathematical claim.

## Relation to earlier work, and what is still needed

Prior [FourEven.lean](FourEven.lean), [FourthBranch.lean](FourthBranch.lean),
[FourthExactTwo.lean](FourthExactTwo.lean), Agent 7's
[UniqueEvenBand.lean](../agent7-cascade-forward/UniqueEvenBand.lean), and
[ResetAncestry.lean](ResetAncestry.lean) supply the essential upstream
lemmas. This contribution eliminates one **complete authentic-root**
branch of a previously established exact two-way fatal gate, which
the earlier pure inverse normal form did not classify as reachable or
unreachable. Original-source verification and an internal overlap audit
are still warranted, and external novelty has not been assessed.

For an eventual #746 nonhalting result, a uniform exclusion of the
remaining even first-reset predecessor across these classes and all
other unclassified fatal-index classes, or a different root-closed
invariant, is necessary. The other globally surviving index
classes remain unaffected.
