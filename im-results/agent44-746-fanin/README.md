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

The final fatal specialization was **initially** checked locally with a temporary signature stub for Agent7's high-valuation theorem. That staging check alone did not establish source compatibility. The subsequent **full original-checked-in-source Lean 4.36.0-rc2 CI succeeded** at [run 42048293246](https://github.com/FlareZ123/bb6/actions/runs/42048293246), commit `6a6fef529e8d1eeff5f5da18100ead1f39df27c5`. The manual-only [workflow](../../.github/workflows/agent44-746-fanin.yml) compiled the unchanged Agent10 first-return grammar, all Agent7 preceding fork and high-valuation dependencies, and the five new Agent44 modules, with no signature stubs. The final `#print axioms` audits for `fatal_unbounded_odd_fanin_four` and `fatal_unbounded_odd_fanin_five` reported exactly **[`propext`, `Classical.choice`, `Quot.sound`]**. All intermediate source modules also passed. The first CI attempt failed on an unrelated, syntactically invalid documentation comment preceding a namespace in Agent7's `FatalValuationPower.lean`; a one-character comment-opening correction (commit `6dee75fdaa3262667fc40b645add7ba302bd9cad`) fixed that parser issue without changing mathematical code, after which the full source CI passed. Upstream physical-machine semantic transport was previously independently audited for the C acceleration. This theorem is directly about source-C first-return resets and does not assert new original-raw-machine halting behavior.

## Exact odd inverse count (second theorem)

The [closed count derivation](ExactCount.md) is now **Lean-kernel proved** for every nonterminal odd inverse valuation position, against the original first-return source grammar. With `2u+5=3^(n+1)*d` and odd `d`, let `oddParameterCount u n` be the number of source-valid `OddParam u t` for `t<n`. [ParameterCountBridge.lean](ParameterCountBridge.lean) proves

```lean
oddParameterCount u n + Nat.log2 (3^n*d) +
  (if 0<n ∧ d=1 then 1 else 0) = 2*n + Nat.log2 d
```

The complete original-source [CI 42052963173](https://github.com/FlareZ123/bb6/actions/runs/42052963173) succeeded; final `#print axioms` used only `propext`, `Classical.choice`, and `Quot.sound`. Six algebraic modules [LogBands.lean](LogBands.lean), [LogStep.lean](LogStep.lean), [Telescope.lean](Telescope.lean), [GeomLog.lean](GeomLog.lean), [GeomBand.lean](GeomBand.lean), [ExactCountLean.lean](ExactCountLean.lean) also passed independent [CI 42052600128](https://github.com/FlareZ123/bb6/actions/runs/42052600128).

For the terminal position `t=n`, [TerminalCount.lean](TerminalCount.lean) proves it contributes exactly when `2^n*d=7` or its dyadic-band predicate is true; a full-source check of that specific file is under way at [CI 42053746058](https://github.com/FlareZ123/bb6/actions/runs/42053746058). Agent7 independently completed the analogous terminal and total-count formalizations in [OddTotalCount.lean](../agent7-cascade-forward/OddTotalCount.lean); its full-source [CI 42053691021](https://github.com/FlareZ123/bb6/actions/runs/42053691021) **succeeded** with only standard logical axioms. This certifies the total admissible-parameter count formula end-to-end. Exact valuation `n+1` requires additionally `3∤d` to rule out higher positions. These formulas count valid *valuation parameters*; uniqueness/injectivity of actual parent heights is handled by [ExactOdd.lean](ExactOdd.lean). They remain intermediate because external novelty and blank-root reachability are unresolved.


## Reproduction and overlap

For finite sanity checks, `n=5` has fatal numerator `2F(5)+5=3^5` and one odd reset parent; `n=130` has valuation four and odd exponents `t=1,3`; `n=491` has valuation eight and odd exponents `t=1,3,6`. These illustrations were checked with Agent10's exact integer predecessor formula; they are independent computation and do not prove the quantified theorem.

The adjacent Agent7 programme already develops full first-parent classifications up to valuations six and proves arbitrarily high 3-adic valuations. This dossier proves a different, universally quantified conclusion about **unbounded distinct source-genuine fan-in**. Agent7 has been contacted at [the collaboration note](../../communications/agent7/20261105T1435Z_agent44-triple-band-fanin.md). Whether the result is externally novel or can be strengthened to a true-root nonreachability obstruction remains open.

**Research implication:** Any proposed universal inverse-cone bound for #746 must tolerate targets with arbitrarily large local odd fan-in. A root-specific uniform obstruction or a verified blank-reachable fatal reset remains necessary to decide this holdout.
