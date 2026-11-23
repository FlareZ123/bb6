# Raw TM62-to-D0 transport for Cryptid D

**Status (23 November 2026): intermediate; no accepted transfer theorem.** The concrete Mathlib-facing adapter exists at [TM62MathlibD0Adapter.lean](./TM62MathlibD0Adapter.lean). Manual run [45136547963](https://github.com/FlareZ123/bb6/actions/runs/45136547963) built the exact pinned upstream/Mathlib closure and upstream Individual module, but the adapter failed typechecking. The external halting theorem is not yet a repository theorem, and this bridge does not establish that the authentic blank root reaches its halting cylinder.

## Pinned source and target semantics

External source:
- Repository: [int-y1/proofs](https://github.com/int-y1/proofs)
- Exact commit: `b77dda5c79fb196d67ce35669e172ad632401c1b`
- Source module: `BusyLean/Individual/1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---.lean`
- Toolchain: Lean 4.36.0-rc1
- Exact Mathlib revision from the pinned `lake-manifest.json`: `dfbc15ea6605db241da9cfd0632bbaf69b67e513`

Repository target:
- `im-results/agent3-portfolio-raw-conjugacy/DTableWitness.lean`, definition `BB6.Portfolio.D0`
- `im-results/agent3-portfolio-raw-conjugacy/MachineConjugacy.lean`, definitions `step`, `run`, and `run_transport`
- `im-results/agent3-portfolio-raw-conjugacy/DStartFinite.lean`, definition `F0Pure`
- `im-results/agent4-coverage-smoke/RelativeTape.lean`, the already proved whole-tape relative/absolute transport

The external machine and D0 use the same six live states A–F ↔ 0–5 and symbols S0/S1 ↔ false/true. Their eleven live entries are:

| External | Read | Write | Move | Next |
|---|---:|---:|---|---:|
| A | 0 | 1 | R | B |
| A | 1 | 0 | R | E |
| B | 0 | 1 | L | C |
| B | 1 | 0 | R | A |
| C | 0 | 1 | L | A |
| C | 1 | 1 | L | D |
| D | 0 | 1 | L | C |
| D | 1 | 1 | L | F |
| E | 0 | 0 | L | C |
| E | 1 | 0 | L | B |
| F | 0 | 1 | L | E |

Both tables return `none` exactly at F/1. This is the standard six-state halting convention.

The separate `CryptidBoundary`/ `BoundaryPadding.delta` encoding instead sends F/1 into frozen state 6. Thus a `CryptidBoundary.run` sink index is one greater than the final live-transition count. That +1 must not appear in a theorem about `BB6.Portfolio.D0`.

## Whole-tape coordinate map

Mathlib's `Turing.Tape Symbol` is head-relative:
- `Tape.nth 0` is the scanned cell;
- positive coordinates are to the right;
- negative coordinates are to the left.

For an external tape T and an absolute head coordinate h, the represented absolute tape is

```lean
absTape T h i := decodeSymbol (T.nth (i - h))
```

and the positioned configuration maps to

```lean
absCfg (q, T, h) : BB6.Portfolio.Cfg :=
  ⟨encodeState q, h, absTape T h⟩
```

The pinned Mathlib module is `Mathlib/Computability/TuringMachine/Tape.lean`. Its relevant lemmas are:
- `Tape.move_right_nth`: after a right move, relative coordinate i observes old coordinate i+1;
- `Tape.move_left_nth`: after a left move, relative coordinate i observes old coordinate i-1;
- `Tape.write_nth`: writing changes exactly relative coordinate zero.

If the head coordinate changes by h'=h+1 on R or h'=h-1 on L, these identities show that the move itself preserves every absolute tape cell. The preceding write changes exactly the old absolute cell h. Therefore the full write-before-move square is equality of the entire infinite tape, not a bounded-window simulation.

## Adapter and exact step accounting

The concrete adapter:
1. imports the actual upstream `tm`, rather than proving only against a copied table;
2. defines a positioned external configuration `(state, absoluteHead, MathlibTape)`;
3. maps `Mathlib.Tape.nth` to `BB6.Bridge.Tape` using the same signed integer coordinates;
4. proves the right- and left-write/move equations from the pinned Mathlib lemmas;
5. proves the external positioned step commutes with `BB6.Bridge.step`, then with `BB6.Portfolio.step D0`;
6. proves exact-n run transport and the equivalence of the undefined next-step condition.

The external `stepNat n` is `n.repeat (fun oc => oc.bind (step tm)) (some c)`. Its `haltsIn n` means exactly n live transitions followed by an undefined next transition. The adapter's `run_project`, `ExtHaltsAt`, `run_toPortfolio`, and `haltsAt_transport` preserve the same n. There is no time shift in D0 semantics.

## Section identity and external halting cylinder

The external section is

```lean
A n ls := default <{{F}} [S1]^n +> ls +> default
```

For `ls=[]`, the scanned cell is blank, cells 1 through n to the right are one, and every other cell is blank. Under the absolute map this is exactly

```lean
BB6.Portfolio.F0Pure n h
```

where `F0Pure n h` has ones precisely at h < i ≤ h+n.

The pinned external theorem `halts_A_mod_3_pow_108` proves that every

```
A(C + 3^108*k, [])
C = 1975700577069254261393123959451562008800234946348086
```

halts. The adapter contains the conditional transfer theorem `D0_halts_on_A_cylinder`, which would place the same halting cylinder in repository D0 semantics with the same primitive halting time once the exact adapter compiles.

The authentic blank start is already identified by the repository's `DAllStarts.every_blank_reaches_unary` theorem:

```lean
run D0 36 (some (blank 0)) = some (F0Pure 9 (-6))
```

The external source also has `reach_9_nil`, but the repository's existing 36-step theorem is the root prefix to reuse. Do not spend another proof checkpoint rebuilding this correspondence.

## Validation boundary

Agent 4's independent abstract [HeadRelativeFunctionAudit.lean](../agent4-cryptid-d0-review/HeadRelativeFunctionAudit.lean) has been compiled locally with Lean 4.36.0-rc2. It checks a copied external table against D0, proves the full-tape write/move square, and transports exact finite runs and halting times. Its transport declarations have axiom profile `[propext, Quot.sound]`; the initial empty-section observation additionally uses `Classical.choice`. This is useful adversarial mathematical evidence, but it does not import Mathlib's quotient tape or the external theorem.

The local Lean 4.36.0-rc2 preflight compiled the repository-side modules `Frontier`, `RelativeTape`, `MachineConjugacy`, `DTableWitness`, and `DStartFinite`. The exact external project uses Lean 4.36.0-rc1, so its pinned Mathlib closure was built in CI rather than locally. Agent 3 identified a missing `List.append_nil` simplification in the positive branch of `A_tape_nth`; Agent 42 applied that fix. The exact-closure run `45136547963` confirms the external module imports, but the adapter itself did not typecheck.

The manual workflow [agent32-cryptid-padding.yml](../../.github/workflows/agent32-cryptid-padding.yml) defaults to `raw_d0_bridge` and excludes the optional 107-call suffix extension. **Run `45136547963` was dispatched and failed at adapter typechecking.** The reported failures concern the `halted`/`step = none` bridge, absolute-tape update correspondence, `Option.map` composition, `List.getI`/`ListBlank` simplification, and the source `tm` versus adapter `ExternalTM` name. Lean's `sorryAx` profiles are error-recovery placeholders for declarations that failed; they are not an accepted transitive axiom audit. See [Agent 2's diagnostic](../../communications/agent32/20261123T082400Z_agent2-raw-adapter-diagnostic.md). Do not describe this adapter or the external theorem as a repository result until a clean compile and transitive axiom audit pass.

## Remaining mathematical target

Even after the bridge is accepted, the difficult question remains whether the authentic orbit from `F0Pure 9 (-6)` reaches any `F0Pure (C + 3^108*k) h`, or whether a genuine invariant excludes all such halting cylinders. The external theorem alone, the finite 2,728,570-state scan, and the closest 21/108 branch match do not answer that root-reachability question.