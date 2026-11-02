# Exact cross-model semantic bridge for the D-start Cryptid

**Status:** intermediate, source-verified Lean theorem, not a BB(6) or blank-tape halting decision. Maintained by Agent 37 on 2026-11-02.

## The semantic incompatibility and its resolution

The D-start six-state Turing machine
`1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`
has two independently written raw-model formalizations in this repository.

- Agent 31's `CryptidBoundary` (restored by SHA-256-checked `im-results/agent31-cryptid-boundary/unpack.py`) has fields `l,h,r,st` and replaces the undefined F/1 transition by the frozen explicit state 6.
- Agent 25's `CryptidA` (`im-results/agent25-cryptid-doublezero/DoubleZero.lean`) has fields `left,bit,right,state` and leaves an undefined F/1 transition stationary at state 5, scanned bit true.

Define `project` from the first to the second: copy all tape components and the machine state except map the explicit frozen state 6 to (state 5, scanned true). Then an exact **total semiconjugacy**, with no assumption of nonhalting, is proved:

```lean
theorem project_step (c : CryptidBoundary.Cfg) :
  project (CryptidBoundary.step c) =
    CryptidA.step (project c)

theorem project_run (n : Nat) (c : CryptidBoundary.Cfg) :
  project (CryptidBoundary.run n c) =
    CryptidA.run n (project c)
```

The `project_run` proof handles the different recursion conventions for the two `run` definitions by using Agent 31's native `run_add`, rather than assuming definitionally identical iterator orientations.

From this, `transfer_f0` transports any exact finite Agent25 run starting in a state other than 6 and **ending in state F scanning 0** to an exact Agent31 raw run. The terminal F/0 prevents the explicit state-6 difference from interfering. This avoids any assumption that the entire trajectory is free of F/1 and is reusable across all such source-verified macros.

## Direct corollaries: arbitrary A-boundary words

The same imported theorem file proves `boundary_a_pairs_triples` and `boundary_a_pairs_triples_nil`, transferring Agent32's fully symbolic A-boundary returns, with all natural m,q,r and unrestricted suffix, to the authenticated `CryptidBoundary.run`:

```text
A( left 0(10)^m11, scan0, right (10)^q 1^(3r) 0 ys )
    --> F( left blank, scan0, right 1^(2m+2q+8r+5) ys )
```

Exact primitive-step cost: `12r² + (6(m+q)+29)r + 2q + 2(m+q+4r)+6`. The independent implicit-blank suffix theorem transfers as well. As these are genuine unbounded quantified identities, they are stronger than any finite trace. They do not imply that the blank orbit enters the stated synthetic tape family.

A follow-on source file `CompleteAReturn.lean` composes these corollaries with Agent31's own `prefix_A` to prove an exact **complete F-to-F branch** for word suffixes of arbitrarily many alternating pairs and triple-one blocks. Treat this additional composition as pending separate CI audit unless its successful manual run is listed below.

## Reproduction and provenance

- Verified source: [CrossModelBridge.lean](./CrossModelBridge.lean), imports the unmodified Agent31 `Boundary.lean` and Agent32 `AAlternating.lean` backed by the unmodified Agent25 `DoubleZero.lean` family.
- Exact manual-only workflow: [agent37-cryptid-halt-model-bridge.yml](../../.github/workflows/agent37-cryptid-halt-model-bridge.yml).
- **Success against both unmodified machine formalizations:** [CI run 41416916169](https://github.com/FlareZ123/bb6/actions/runs/41416916169), Lean 4.36.0-rc2. The log reports `[propext]` on `project_step`, `project_run`, `transfer_f0`; `[propext, Quot.sound]` on both parametric A corollaries. No `sorryAx`, `admit`, or independent semantic assumption.
- All runs use the real original-model sources, not a mock. Earlier failing CI runs are [41416216160](https://github.com/FlareZ123/bb6/actions/runs/41416216160), [41416443291](https://github.com/FlareZ123/bb6/actions/runs/41416443291), and [41416731517](https://github.com/FlareZ123/bb6/actions/runs/41416731517); the final successful full-source revision fixed their typing/proof issues.

## Open mathematical tasks

Compose the actual blank-origin F sections end to end using the now-unified symbolic macros. Verify all F/0 suffix traces and seek a global closed forward invariant or decisive halting witness. The halting language of this machine is unknown at its actual blank start; BB(6) has not been determined. Compare the full return equations to @-d's published Cryptid reductions before claiming historical priority. This work belongs under `im-results/`; it does not meet the repo's requirement for publishable standalone results in `results/`.
