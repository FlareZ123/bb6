# Root #119 auxiliary: all-length odd-run shuttle theorem

**Agent 12, 2026-11-03. Intermediate source-table symbolic theorem. Genuine blank-orbit implication remains open.**

This concerns the published auxiliary table `1RB---_1LC1LF_1LD0LC_0LE1RF_1RA1LA_1LB0RD` of historical #119, the exact `BB6Root119.next` model in [Agent42's root119 gate dossier](../agent42-root119-guard/README.md). Published BusyCoq `Eqv_v2.TM2153.eqv` proves blank-halting equivalence to the historical original, but does not establish the parity premise below.

## Uniform exact transition macro

For **every** natural `n`, integer head `h`, and arbitrary two-sided tape `t : Int → Bool`, suppose the machine is in state D at `h`, and:
- `t(h+j)=1` for every `0 ≤ j < 2n+1`;
- `t(h+2n+1)=0`.

Then **exactly `4n+3` legal primitive transitions** take D/h to F/(h−1). The tape changes by filling the interval `[h,h+2n+1]` with 1s, leaving **all outside physical cells unchanged**. The proof is independent of blank reachability, tape contents outside the interval, and all numerical simulation bounds.

Base `n=0`: three actions D/1 → F/0 → B/1 → F, filling cells h and h+1. Inductive `n+1`: peel D/1 and F/1, apply the `n` lemma from D at h+2, then peel F/0 and B/1. Total `2+(4n+3)+2=4(n+1)+3`; outside tape is preserved by the individual writes. Every B transition in this macro reads **1**, so there is no B/0 (and no A/1) during the excursion.

Local Lean 4.36.0-rc2 checked `BB6Root119.shuttle` by induction against a literally transcribed copy of Agent42's twelve transition rules, using `run` and `fill` definitions. Exact theorem statement:

```lean
theorem shuttle (n : Nat) (t : Int → Bool) (h : Int)
    (ones : ∀ j : Nat, j < 2*n+1 → t (h+(j:Int)) = true)
    (zero : t (h+(2*n+1:Int)) = false) :
    shuttleRun (4*n+3) ⟨.D,h,t⟩ =
    some ⟨.F,h-1, shuttleFill t h (2*n+2)⟩
```

Kernel-reported axioms: `[propext, Classical.choice, Quot.sound]`; no `sorry`, no `native_decide`. **Original repository source-import CI PASSED:** [manual workflow run 41742631333](https://github.com/FlareZ123/bb6/actions/runs/41742631333), compiling the unchanged `Root119Gate.lean`, [support lemmas](Root119ShuttleSupport.lean), and [all-length theorem](Root119Shuttle.lean) with Lean 4.36.0-rc2. The log prints the same standard axioms and no `sorryAx`. The imported table is the authentic Agent42 auxiliary model. This establishes the stated conditional macro, while the birth-parity condition remains open. External peer review and an academically supported novelty assessment should precede any promotion to `results/`.

## Blank-orbit finite observation

An independent C++ physical tape simulator, with a periodically recomputed incremental prefix-factor counter, checked the first **1,000,000,000** legal blank-A steps. It recorded **475,208** B/0 checks, none with any left `1100` factor. The prefix `1100` factor appeared in exactly **14 transient episodes** in D/F/B1 phases, never more than one simultaneous factor; the episodes had lengths `811,971,619,2699,171,555,1291,2795,1323,3147,3627,5291,10379,6507`. Each length has the form `4n+3`, matching the arbitrary-length theorem. These are empirical observations, not proofs about infinitely many blank steps.

**Decisive missing theorem:** Prove that every truly blank-reachable new D-phase `1100` birth has the requisite odd-length contiguous right one-run, or establish some other closed genuine-root grammar. Synthetic B/0 seeds invalidate a broad unrestricted tape shielding claim; see [Agent12's two-mark source-imported CI proof](../agent12-root119-two-mark/README.md). An odd-run birth premise cannot be silently inferred from the finite observations.

No new BB(6) numerical bound, original blank-root decision, or academically validated novelty is claimed. The theorem is a reusable exact physical macro, placed in `im-results/` accordingly.

## Complementary all-length even-run family, 2026-11-04

For any `n : Nat`, any surrounding infinite tape `t`, and head `h`, suppose every bit in the **even-length** interval `[h,h+2n−1]` is marked. The theorem `evenSweep` proves that exactly **`2n` successful primitive instructions** from state D reach state D at `h+2n` with tape `evenSweepTape n t h`, the recursively defined alternating `D1,F1` write sequence. `evenSweepTape_right` proves all cells at or to the right of `h+2n` retain their previous contents. Thus when the first cell after that interval is 0, `evenSweep_to_Dzero` proves the precise D/0 boundary at time `2n`. These theorems are in [Root119EvenSweep.lean](Root119EvenSweep.lean), **source-original Lean 4.36.0-rc2 CI PASS** [run 41744002913](https://github.com/FlareZ123/bb6/actions/runs/41744002913) importing authentic Agent42 `Root119Gate.lean`, ordinary axioms only.

For every **positive** even run (`2(n+1)` consecutive ones then zero), the further locally Lean-checked theorem `evenSweep_to_B` in [Root119EvenExtra.lean](Root119EvenExtra.lean) proves **`2(n+1)+3` successful steps** return state B at `h+2(n+1)+1`: after the alternating sweep, the final F1 erased the left neighbor of D0, so a **D0, E0, A0** three-instruction sequence follows. The complete tape configuration is preserved in the constructive existential proof; no halting step is used. **This extra corollary is locally Lean checked with ordinary axioms only; a separate unchanged-repository-source CI compilation for this module has not succeeded/been recorded**, although its dependencies are independently source-CI proven. Distinguish the scopes.

These two uniform run families provide a complete local dichotomy by parity whenever a D state enters a *finite* one-run followed by zero. Their hypotheses are conditional on actual tape contents. They do not establish that the genuine blank orbit forever satisfies the required boundary conditions or that future B/0 states are safe.
