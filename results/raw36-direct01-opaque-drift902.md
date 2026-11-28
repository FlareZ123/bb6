# A source-checked 902-step opaque-tail nonhalting invariant for a Raw36 holdout

**Status (2026-11-28): Lean 4.36.0-rc2 kernel-accepted locally and in independent CI, using only `propext` and `Quot.sound`.** This result settles one literal six-state/two-symbol partial machine under all compatible completions. It does **not** establish BB(6), nor does it by itself close the entire Raw36 direct D1=0LB parent.

## Exact machine and result

In the standard 6-state 2-symbol convention, the transition table is:

```text
1RB1LF_1RC0RE_0RD1RA_0LD0LB_1LF---_0LA1LC
```

Here `---` is undefined, in the state E / read-one position. The machine is the B1=0RE leaf within the direct Raw36 D1=0LB partial cylinder `1RB---_1RC---_0RD---_0LD0LB_------_------`.

**Theorem.** For every complete Turing machine `m` whose transitions agree with the eleven specified entries of the displayed table, the blank-tape computation of `m` never halts.

The exact Lean statement generated in `Raw36D101Hard10.lean` is

```lean
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 14958 (fun _ => 902)
    entry (by intro n; decide) growth m hm
```

## Explicit uniform invariant

Use the `SweepPumping` zipper convention: `Z0 = (q,l,r)`, where `l` includes the tape cell under the head, `r` consists of the cells strictly to its right, and unrepresented cells are blank. Let

```text
P = 11111010
W = 01001001001001001001
```

Starting at the all-zero tape, **exactly 14,958 machine steps** reach the state `(C, [], P ++ T)`, where `T` is an explicit 106-bit fixed finite right suffix (determined unambiguously by `derive_drift.py`). The decisive uniform computation is

```lean
theorem one (R : List Bool) :
    run0 table 902 ⟨2,[],pre++R⟩ =
      some ⟨2,[],pre++block++R⟩ := by rfl
```

This is a **literal 902-step identity for arbitrary `R`**. The transition sequence reads only the fixed eight-bit prefix and freshly blank cells to its left; in particular it never examines `R`. Consequently, the configurations

```text
(C, [], P ++ W^n ++ T),  n = 0,1,2,...
```

each have a successor after precisely 902 steps with `n` incremented by one. They supply arbitrarily long defined computation prefixes, which proves nonhalting for every compatible completion. No finite-step empirical extrapolation is required: both the entry and the universal transition are formally checked.

## Reproducible formal evidence

The sole source generator is [`im-results/agent7-raw36-direct/derive_drift.py`](../im-results/agent7-raw36-direct/derive_drift.py). The reproducible GitHub Actions workflow is [`agent7-raw36-drift902.yml`](../.github/workflows/agent7-raw36-drift902.yml). It reconstructs the exact literal finite computation in chunks, verifies the arbitrary-tail identity, proves the induction using `SweepPumping.never_of_growth`, and checks the axiom report.

On 2026-11-28 at approximately 08:21 UTC, after correcting only a final simplification of the 14,958-step entry, the generated complete Lean source compiled successfully with the repository's precompiled `SweepPumping.olean` and `SparseZipper.olean` using **Lean 4.36.0-rc2**. The kernel reported:

```text
'BB6.Agent7Raw36D101Hard10.one' depends on axioms: [propext]
'BB6.Agent7Raw36D101Hard10.growth' depends on axioms: [propext]
'BB6.Agent7Raw36D101Hard10.entry' depends on axioms: [propext, Quot.sound]
'BB6.Agent7Raw36D101Hard10.never' depends on axioms: [propext, Quot.sound]
```

The initial CI run [46125040682](https://github.com/FlareZ123/bb6/actions/runs/46125040682) independently accepted `one` and `growth` but failed at the final `entry` elaboration because its tactic omitted unfolding the literal `pre` and `tail` constants and normalizing a nested numeral sum. The corrected source was locally kernel-accepted without `sorryAx`, and subsequently the independent full-source CI [run 46125317196](https://github.com/FlareZ123/bb6/actions/runs/46125317196) **completed successfully** and retained [artifact 15255990116](https://github.com/FlareZ123/bb6/actions/runs/46125317196/artifacts/15255990116) with the complete generated source, olean dependency manifest and axiom audit.

The proof is directly relevant to the weighted-450 Raw36 D1=0LB audit: an exact source-indexed canonical tree has **320 OPEN leaf tables**, of which this was the last without a discovered nonhalting candidate. The other **319** have recorded exact-table FAR, N-gram, RLE, modular, or periodic-stack candidates in `im-results/agent7-raw36-direct/evidence01.xz.b64` and `extra-hard01.json`. Those 319 **remain distinct proof obligations until their original Lean audits succeed**, and the parent 450-weighted Cover is not claimed here.

## Generalizable mathematical mechanism

This example illustrates a finite **opaque-tail insertion invariant**: a machine reaches a frame `(q, [], P ++ R)` and, without inspecting `R`, returns after a positive fixed number of transitions to `(q, [], P ++ W ++ R)` for a nonempty block `W`. Such a frame yields a direct induction on the number of inserted blocks with no requirement for a regular-language approximation of the rest of the tape. The distinction between a concrete observed recurrent pattern and a universal arbitrary-tail equality is essential to the proof.
