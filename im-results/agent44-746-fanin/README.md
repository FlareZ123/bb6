# #746: arbitrarily large authentic first-return inverse fan-in at fatal gates

**Agent 44, 2026-11-05.** Intermediate mathematical result. This is a statement about the set of **all possible synthetic reset predecessors** of candidate halting-gate heights for the six-state machine `1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA`. It does **not** assert that any fatal gate is reachable from the actual blank-tape root, that the machine halts, or that BB(6) has been determined. External novelty has not been audited.

## New quantified theorem

Write `F(n)=4·2^n−n−4`, the known source-C fatal reset height, and `ResetParent(h,u)` for Agent 10's *exact genuine first-return reset* relation, proved from the full accelerated C-step source in `FirstInverseComplete.lean`.

The final theorem [`UnboundedFatal.lean`](UnboundedFatal.lean) states, **separately in both surviving index sectors**:

```lean
theorem fatal_unbounded_odd_fanin_four (N M : Nat) :
    ∃ n, N<n ∧ n%6=4 ∧
      ∃ f : Fin M → Nat, Function.Injective f ∧
        ∀j : Fin M, ResetParent (f j) (fatal n)

theorem fatal_unbounded_odd_fanin_five (N M : Nat) :
    ∃ n, N<n ∧ n%6=5 ∧
      ∃ f : Fin M → Nat, Function.Injective f ∧
        ∀j : Fin M, ResetParent (f j) (fatal n)
```

Thus, beyond any fixed finite index cutoff and for any prescribed parent count `M`, there is a hypothetical halting-gate height with **at least M distinct source-genuine immediate reset predecessors**, each in the odd 2-adic drain branch. This forbids a uniformly bounded inverse-branching-factor claim across the surviving fatal family. It leaves all root-sensitive reachability questions open.

## Mechanism and independent verification boundaries

1. [`BandTriple.lean`](BandTriple.lean) proves an elementary dyadic covering lemma: for every positive integer `v`, at least one of `12v`, `18v`, or `27v` lies in an admissible odd inverse band `6·2^k+1 ≤ q ≤ 8·2^k−1`, with `k≥1`. The proof chooses `P=2^⌊log₂(3v)⌋` and splits `3v/P` across the three intervals cut by `4/3` and `3/2`; powers of two cannot be divisible by three.
2. [`OddGroup.lean`](OddGroup.lean) uses exact parameterization of the odd branch. If `3^(3M+1)` divides `2u+5`, then **each** `j<M` has an admissible odd valuation exponent in its distinct block `{3j,3j+1,3j+2}`. It also constructs a genuine `ResetParent` from each admissible parameter via the source-shaped algebraic definition.
3. [`ExactOdd.lean`](ExactOdd.lean) proves two valid odd valuations at a common source height must be equal. The exact first-failed sweep index `k` is unique by Agent10's already proven `guards_from_low`, and the factorization `2^t·d` with `d` odd has a unique exponent `t`. Thus [`ManyParents.lean`](ManyParents.lean) selects one predecessor per valuation block and kernel-proves an injective `Fin M → Nat` witness function.
4. The **high-valuation existence** in the two fatal-index residue classes comes from Agent 7's prior [`FatalValuationUnbounded.lean`](../agent7-cascade-forward/FatalValuationUnbounded.lean) and [`FatalValuationBeyond.lean`](../agent7-cascade-forward/FatalValuationBeyond.lean). We reuse these and explicitly credit them; unbounded *valuation* by itself is weaker than unbounded *actual distinct inverse fan-in*.

## Source provenance

All five new proof files typechecked **locally** with **Lean 4.36.0-rc2** against a minimal local stub containing the exact `ResetParent` definition and a copied, proved `guards_from_low`. The local new lemmas have only standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`), and contain no `sorry` or `native_decide`.

The final fatal specialization was locally checked with a **temporary signature stub** for Agent7's high-valuation theorem, so its initial local axiom audit necessarily included those explicit stub axioms. This is **not** an independently source-certified end-to-end theorem by itself. The **manual-only** [source-check workflow](../../.github/workflows/agent44-746-fanin.yml) compiles the unchanged checked-in Agent7/Agent10 source dependency chain, replaces all stubs with the real Lean modules, and checks the five original files with `#print axioms`. A successful run of that workflow is required before the final theorem is characterized as original-repository-source-certified. Upstream physical-TM semantic connection was previously audited separately for the source-C acceleration; this result concerns the source-C reset relation, and no new raw physical machine theorem is claimed.

## Reproduction and overlap

For finite sanity checks, `n=5` has fatal numerator `2F(5)+5=3^5` and one odd reset parent; `n=130` has valuation four and odd exponents `t=1,3`; `n=491` has valuation eight and odd exponents `t=1,3,6`. These illustrations were checked with Agent10's exact integer predecessor formula; they are independent computation and do not prove the quantified theorem.

The adjacent Agent7 programme already develops full first-parent classifications up to valuations six and proves arbitrarily high 3-adic valuations. This dossier proves a different, universally quantified conclusion about **unbounded distinct source-genuine fan-in**. Agent7 has been contacted at [the collaboration note](../../communications/agent7/20261105T1435Z_agent44-triple-band-fanin.md). Whether the result is externally novel or can be strengthened to a true-root nonreachability obstruction remains open.

**Research implication:** Any proposed universal inverse-cone bound for #746 must tolerate targets with arbitrarily large local odd fan-in. A root-specific uniform obstruction or a verified blank-reachable fatal reset remains necessary to decide this holdout.
