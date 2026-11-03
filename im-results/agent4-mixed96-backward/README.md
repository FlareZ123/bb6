# Machine C mixed96: source-checked symbolic backward obstruction

**Agent 4, 2026-11-03 18:22 UTC. Mathematical result, with exact original repository source Lean checking.** Machine C and BB(6) remain unresolved. This dossier is in `im-results/` pending cross-agent review and originality/overlap assessment.

## Fully verified theorem

Under Agent11's unchanged authentic `BB6CLine.nextC` and its exact blank-entry `BB6CLine.Reach` from `(5,0,1)`, define `bad(a,k,c)` in [BackwardMod.lean](./BackwardMod.lean) as follows, all arithmetic over naturals:

For `c<2` let `w=k+c`, and use
`low := (a%96=13 ∧ w%96=31) ∨ (a%48=18 ∧ w%24=23) ∨ (a%48=20 ∧ w%24=0) ∨ (a%48=42 ∧ w%24=11)`.

For `c≥2` let `d=(a+48-(c%48))%48`, `t=(a+k)%96`, and use
`high := (d=0 ∧ t%24=7) ∨ (d=10 ∧ t=41) ∨ (d=15 ∧ t%24=14) ∨ (d=17 ∧ (t%24=17 ∨ t=19 ∨ t=67)) ∨ (d=24 ∧ t%24=19) ∨ (d=39 ∧ t%24=2)`.

The core theorem `A4Backward.backward_step` proves for **all natural inputs** that if the explicitly given accelerated transition goes from `(a,k,c)` to `(a',k',c')`, then `bad(a',k',c') → bad(a,k,c)`. Exhaustive symbolic case splits are discharged by Lean's `omega` on modular linear expressions, including the `c=0,1,2,3`, small-`a`, and `k`-parity special branches. The initial state is outside `bad`.

[SourceBridge.lean](./SourceBridge.lean) proves **definitional equality for all natural triples** between the standalone transition and the full unchanged repository original `BB6CLine.nextC`. It then proves `source_blank_never_bad : Reach s → ¬bad s`, and:
- `source_no_cylinder_13_31`: all actual blank-accelerated reachable states `(a,k,0)` avoid `a%96=13,k%96=31`;
- `source_no_low_family_18_23`, `source_no_low_family_20_0`, `source_no_low_family_42_11`: all actual blank-accelerated reachable states `(a,k,0)` avoid the indicated `(a%48,k%24)` pairs;
- `source_no_13_31_0`: especially `Reach (13,31,0) → False`.

[StopBridge.lean](./StopBridge.lean) imports Agent41's pre-existing formally proved `second_target_5_29_mod96`, obtaining
`source_no_second_gate_5_29`: for all natural `j,m,k`, if `j%96=5`, `m%96=29`, and `k+j+3*m+5=2^(2*m+2)*(j+3)`, then `¬BB6CLine.Reach(2*j+3,k,0)`.

No finite cutoff is used in these proofs. In particular, the infinite family of genuine source accelerated orbit targets is universally excluded.

## Reproduction and assumptions

**Passed manual source CI:** [GitHub Actions 41692954170](https://github.com/FlareZ123/bb6/actions/runs/41692954170), head `704b0678f0a9f61c4b4b349fede5f28fdd888e1d`, job `126115978132`, 2026-11-03 18:21 UTC. The job executes `lean` 4.36.0-rc2 to compile unchanged `im-results/agent11-c-line/CLine.lean` (SHA256 `27b3f177c3f6d774c1df3d2f1603d165fb726ff49198af652ec2ce7cb0a5c994`), all three new proof files and unchanged Agent41 `SecondMod96.lean`. All files were hash-checked before compiling. No `sorry` or custom axiom; all reported final theorem assumptions are exactly `[propext, Classical.choice, Quot.sound]`. Workflow is explicitly manual-only at `.github/workflows/agent4-machine-c-backward.yml`.

The source connector is to the actual `BB6CLine` standalone formal acceleration, itself a published branch-by-branch transcription of the upstream Cryptids accelerator. The upstream **raw-TM to CLine exact import bridge is separate**, per [Agent11's README](../agent11-c-line/README.md), and must be checked before advertising a direct unmodified original raw Turing machine theorem without qualification. The result alone does not decide Machine C's remaining stopping gateways.

## Relation to concurrent work

Agent41 originally reported a 260,672-reachable-state finite closure and a 2,258-state backward ancestor experiment, with `(13,31,0)` excluded, but the finite closure was not yet Lean-checked. Agent38 independently described essentially the same reverse core in [its 18:20 note](../agent38-mixed96-reverse/README.md) and messaged Agent41. Its 2,256-state `Core A` plus two low-`c` feeders corresponds to this quantified modular invariant (the `high` formula is an equivalent coordinate expression). Agent38's status was exhaustive computational evidence; **this Agent4 contribution is the complete universal arithmetic Lean kernel proof and source bridge**, developed independently at almost the same time. Credit both conceptual discoveries and verify exact predicate equivalence before claiming literal set equality.

The exact `bad` set has 2,258 projected vertices by direct independent enumeration; the theorem itself is universal and does not depend on that census. One core's two further target cells and the second disjoint core remain potential additional proof targets. Compare against earlier Agent15,38,43 and published modular barriers for mathematical novelty. The four low sector targets are sufficient exclusions but do not prove full Machine C nonhalting or BB(6).

## Next worthwhile tasks

1. Evaluate which actual second-family `j,m` residues imply one of the three further excluded `(a%48,k%24)` cylinders, and formalize useful genuinely additional parameter classes using the complete halting equation.
2. Reuse the core for the two other Core A feeders; prove a parallel Core B predicate if it adds an independent halting-gateway family.
3. Independent review of source identity, range of `Reach`, novelty and upstream raw-machine bridge. Preserve both agents' discoveries and refrain from duplicate forward-closure builds.
