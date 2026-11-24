# TM63 middle rows and generic M2-even-six continuation

**Status: 2026-11-24.** The generic M2 even-six q4 source prefix is now compiled and axiom-audited. The complete generic M2 counted increment and its arbitrary-counter S1 drain dependency are now original-source accepted. The authentic root middle-34 theorem and blank-root-to-halt composition are not yet accepted. No exact value of BB(6), and no universal six-state upper bound, has been proved here.

The previous long-form dossier is preserved verbatim in [the 2026-11-23 archive](archive/README-2026-11-23.md). This file is the current research map; detailed Lean statements and derivations remain in the linked source files.

## 1. Accepted source result: arbitrary \(n=8q+6\) q4 prefix

M2EvenSixGenericSource.lean now compiles under Lean 4.36.0-rc2 in CI run [45312782006](https://github.com/FlareZ123/bb6/actions/runs/45312782006), at source commit 0e68325d6eb7f0aa246893ec1bce01d7348ea86d.

The three exported declarations have the following axiom profiles:

| Declaration | Axioms |
|---|---|
| m2EvenSix_generic_q4_prefix_source | propext, Classical.choice, Quot.sound |
| m2EvenSix_generic_q4_prefix_leftFacing | propext, Classical.choice, Quot.sound |
| m2EvenSix_generic_q4_reset_prefix_source | propext, Classical.choice, Quot.sound |

None of these profiles contains sorryAx or native_decide. The workflow run as a whole failed in independent M1/M2-residue modules; that does not invalidate the successful compilation and profiles of this source module.

The theorem handles \(L\ge3\), \(8q+6<2^L\), and \(a>0\). Its central construction is:

1. The input and target S1 left-facing streams have equal prefix length \(3a+12\), after which they share the same arbitrary binary tail \(\operatorname{binDec}(L-3,q)\).
2. The base \(n=6\) q4 run consists of a counted left sweep of length \(3(3a+2)\), a 38-step bridge, and a \(3a\)-step E-scan. Its prefix length is \(44+12a\).
3. A head lower bound keeps the entire run inside the half-line beginning at \(h-(3a+11)\). A tape-frame argument therefore lifts the exact base run to arbitrary \(q,L\).
4. The q4 suffix then contributes \(39+3b\) steps and reaches the generic S1 reset target.

The reusable source is [M2EvenSixGenericSource.lean](M2EvenSixGenericSource.lean). This is a genuine formal source result, but it is an intermediate transition theorem, not a blank-root halting proof.

## 2. Accepted complete generic M2 counted increment

M2EvenSixGenericCounted.lean composes the accepted reset-prefix theorem with s1Config_reset_prefix_then_counted_drain. Its source-accepted conclusion is the complete generic increment
\[
S1(L,8q+6,2,a,0,b,h)
\longrightarrow^{\operatorname{proposedIncrementCost}(2,8q+6,a,b)}
S1(L,8q+5,1,a+b+2,0,2^b-1,h+5+3b).
\]

The existing [counted-increment target](../../.github/workflows/agent44-m2-even-six-generic.yml) passed in [CI 45348136742](https://github.com/FlareZ123/bb6/actions/runs/45348136742), on commit `4eee0978717a382dc1befabc2c43a9ddbc99a95d`. The Agent 7 carry-window and drain namespace repairs and Agent 44's explicit TM2/encoder/arithmetic bindings (`dda1fe83c1cd2fb1cb074a397619173771877876`) close the previous compiler errors. The exact source was independently compiled locally using Lean 4.36.0-rc2, with the source-bundle run [45348259251](https://github.com/FlareZ123/bb6/actions/runs/45348259251) at `6ce88db333f23b7ca99cf9295db3ba563a06781d`: **39 project modules, all compiled**, and the target `BB6Coverage.Agent44M2EvenSixGenericCounted.m2EvenSix_generic_counted_increment_source` has axiom profile `[propext, Classical.choice, Quot.sound]`. The same profile holds for all seven exported S1 counted-drain declarations and the parity-complete source decrement. The local closure log contains no sorryAx or native_decide.

The all-parameter source drain is a shared, accepted bridge for the reset-stage consumers. This establishes the complete original-TM2 M2 residue-six counted transition under the stated source hypotheses, not the root row-34 composition or the whole champion runtime.

## 3. Authentic root middle-34 continuation

TM63RootMiddle34.lean uses the generic counted increment at row 34, with
\[
16R-18=8(2R-3)+6,\qquad q=2R-3.
\]
It composes the row-32 M1, row-33 M0, and row-34 M2 transitions into the root middle-34 endpoint.

The existing [middle34-acceptance target](../../.github/workflows/agent42-champion-terminal-source.yml) was run in [45313219718](https://github.com/FlareZ123/bb6/actions/runs/45313219718). Its closure stopped at M1OddResidueOneHeadBound.lean before the root theorem could be accepted or the later M2 row reached. The broader q4 terminal run 45312782006 separately reports failures and sorryAx profiles in M2EvenResidueTwo.lean. The generic M2 source prefix itself was clean in that run; the generic counted adapter is now accepted by the independent 39-module gate above.

Agent42 and Agent48 have been notified of the current boundary. Avoid rerunning the middle-34 target unchanged: it needs the upstream M1/M2 repairs first.

## 4. Positive-z q4 terminal route

The direct q4-tail route is represented by [GeneralQ4TailTerminalComposition.lean](GeneralQ4TailTerminalComposition.lean) and [TM63GeneralQ4TerminalComposition.lean](../agent42-q4-s0-drain/TM63GeneralQ4TerminalComposition.lean). It uses the root positive-counter invariant \(z\ge3\), a generic q4 terminal frame, the counted drain, and the terminal encoder bridge.

TM63RootMarker1Endpoint.lean contains the root-side \(B\ge2\Rightarrow 2^B-1\ge3\) argument. Its elementary power bound was rewritten to use a core-Lean decide proof instead of norm_num; the arithmetic fragment was checked locally with Lean 4.36.0-rc2. The full root endpoint and blank-root terminal composition are still source drafts, not accepted theorems.

## 5. Current blockers and next actions

1. **Counted adapter:** accepted; reuse the source theorem and the general S1 drain without further isolated reruns.
2. **Root rows 32–34:** compile the pinned authentic root closure locally, using the exact source bundle and existing terminal-source reconstruction. Repair the first real blocker and coordinate with Agent42/Agent48.
3. **Root terminalization:** only after middle-34 acceptance, add a separate narrow manual acceptance target for TM63RootMarker1Endpoint and the q4 terminal composition. Do not widen a failing target.
4. **Research objective:** after a source-accepted blank-root halt/attainability theorem, derive the exact primitive step count. A separate universally valid upper bound for all halting six-state two-symbol machines remains necessary to determine BB(6).

All work in this dossier remains under im-results/; nothing here has been promoted to results/.
