# Agent 39: three genuine blank-root exclusions in BB429's 1021 sector

**2026-11-04 18:58 UTC. Intermediate all-natural source-connected mathematical progress.** The original six-state holdout is `1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA` (the upstream DeepMind Cryptids #429 accelerator). None of the three classes is an observed halting witness, and the result does **not** decide this machine or BB(6). Assess external novelty before any `results/` promotion.

## Exact theorems

For every `n,a,b : Nat` in the **genuine accelerated blank orbit** of the repository's unchanged `BB429.next` (seed `(0,0)`), the three named Lean theorems establish

```lean
BB429.run n (0,0) = some (a,b) →
  b+1=2*a →
    a%16384≠9213 ∧ a%16384≠11261 ∧ a%16384≠12285
```

These are three **entire infinite terminal congruence cylinders** in the prior surviving `a≡1021 (mod1024)` class. All `q≥0` are covered; no finite trace or maximum value of `n` is assumed. Each is disjoint from Agents1/6/18/30's previously excluded sectors. There remain 13 of the 16 lifts of `1021 (mod1024)` under this three-class filter.

Source: [`BB429No12285mod16384.lean`](BB429No12285mod16384.lean) and [`BB429No1021More.lean`](BB429No1021More.lean). The second module imports the first and proves `blank_halt_not_three_1021_lifts` as an axiom-audited conjunction.

**Unchanged-repository-source verification:** all dependencies `BB429Rank.lean`, `BB429Mod8.lean`, `BB429NewResidue.lean`, and both new modules compiled in [manual CI 41891893699](https://github.com/FlareZ123/bb6/actions/runs/41891893699) (finished 2026-11-04 18:56 UTC). The direct single-lift proof passed in [CI 41891134078](https://github.com/FlareZ123/bb6/actions/runs/41891134078). Every printed final theorem's axioms are **exactly `[propext, Classical.choice, Quot.sound]`**. No `sorryAx`, `admit`, `native_decide`, facade axioms or copied external `next` definition in these source checks. Workflow: [`agent39-429-1021-source.yml`](../../.github/workflows/agent39-429-1021-source.yml), manual-only.

## Complete inverse argument

The previously proven `BB429Mod8.all_blank_returns_allowed` is a forward inductive invariant for all actual blank-root accelerated sections. The previous Agent6 `BB429NewResidue.odd_back` theorem exhausts **all** predecessors of any odd target with first counter at least 13:

1. First branch: target `(a,b)` comes from `((a-3)/2,b+a)`.
2. Other branch: an earlier state `(x,y)` must solve `4*x+26=4*a+b`, `2*y=b+4`, and `b%4=2`.

In each newly forbidden family, a backwards affine spine follows the first branch. At every node, the second branch either violates its exact arithmetic guard or yields a source state contradicting the verified `Allowed` invariant. The spine uniformly decreases the first counter, and its terminal predecessor (or short side branch) violates `Allowed`.

For the simplest `12285 (mod16384)` family, write `a=16384q+12285`, `b=32768q+24569`. Ten successive first-branch inverses have exact first-counter constants
`12285→6141→3069→1533→765→381→189→93→45→21→9` and coefficients
`16384→8192→4096→2048→1024→512→256→128→64→32→16` multiplying `q`. Every side branch contradicts `Allowed`. The final `(16q+9,65504q+49091)` has first counter `1 (mod8)` and second counter `3 (mod4)`, hence violates `Allowed` at any `q`.

For `11261 (mod16384)`, ten first-branch inverses likewise end at an even state `(16q+8,65504q+44997)` with incompatible second-counter parity. The side branch after nine levels has `(16400q+11257,32736q+22491)`, itself violating `Allowed`.

For `9213 (mod16384)`, nine first-branch inverses lead to `(32q+15,65472q+36794)`. Its first parent is `(16q+6,65504q+36809)` and violates `Allowed`. The other parent `(16400q+9207,32736q+18399)` is ruled out by an exact further odd-predecessor split and the Agent6 `even_back` theorem. The forced even grandparent `(20484q+11500,24568q+13803)` has forbidden first/second parity. No preimage is omitted, including `q=0`.

The proof uses `omega` on symbolic linear equalities for **arbitrary** natural `q`; it does not infer a universal result from sampled q values.

## Native raw-machine source bridge and gate counts

[`SourceRawHalt1021.lean`](SourceRawHalt1021.lean) imports Agent1's earlier **original-Cryptids-source-certified** `SourceRawHalt86` and the new three-class theorem. It transports the three exclusions into the pinned `BusyBeaver.BB6.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA` high-level source using the previously proven `BB429SourceMod16.source_run_to_local` and exact source halting-line equivalence. It also proves an iff statement `raw_halts_iff_86_plus_three` for the genuine raw `IsHalt target`, conditional only on the stated, necessary 86/2048 gate predicates and exclusion of the three 16384 residues. No such remaining gate is asserted reachable.

Native pinned original Cryptids SHA: `c86f15861709b76042998c5211c7b2f83991621b`; original Lean 4.35.0-rc4. [Native manual CI 41892188899](https://github.com/FlareZ123/bb6/actions/runs/41892188899) was dispatched 2026-11-04 18:57 UTC and **was pending when this dossier was first written**. Do not equate the passing **repository-source** check with this still-pending **upstream-original raw-machine** check. The native workflow is [`agent39-429-1021-native.yml`](../../.github/workflows/agent39-429-1021-native.yml).

As a separate exact computational synthesis, the conjunction of already published *accelerated-source* gate restrictions from Agent30's `38/1024`, Agent1's two `2048` cuts, Agent6's four `8192` cuts, and the three exclusions here yields **581 of 16,384 possible necessary residue classes** under the combined filter, computed by explicit enumeration of all `a%16384` residues. This is a residue-filter count, not undecided-machine count or a BB(6) upper bound. Some constituent original-upstream source audits remain pending or encountered runner disk quota failures, so the single complete native-`IsHalt` iff theorem for this **full 581-class conjunction** is not claimed. Our own native theorem currently composes with previously source-verified Agent1's 86/2048 gate result.

## Research value and next decision target

The previously unresolved `1021 (mod1024)` sector now has **three all-natural genuine blank-root terminal exclusions**. These depend on root-sensitive modular admissibility, not generic synthetic reachability. The same predecessor grammar is useful for reviewing the remaining 13 lifts or seeking a stronger closed family. Avoid blindly lifting to ever larger moduli: a genuinely complete halting sector or an all-time forward blank-reachability invariant is substantially more consequential. Compare overlaps with Agents1,6,18,30 before extending.

The exact BB(6) value and even this particular machine's eventual halting remain open.
