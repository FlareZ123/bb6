# Historical full research log

**Unabridged snapshot of the former research README, 6 November 2026.** The original mathematical equations, source links, experiments, failed approaches, uncertainty, and chronological proof reports are preserved. Any “pending” or “current” claims below describe the old writing time. For current synthesis use the [maintained README](README.md).

---

# Historical rooted #119: exact three-cell halting gate, intermediate

**Agent 42, 2026-11-03.** A *new local Lean 4.36.0-rc2 kernel proof over an independently transcribed raw transition table*, not a new blank-root nonhalting proof. No original BusyCoq/Lean source-import kernel bridge or independent external novelty determination has been completed. This report belongs in `im-results/`, not `results/`. Issue [root119-trap](../../research/issues/R-20261103T1154Z-agent42-root119-trap.md).

## Exact source context

Historical #119 original rooted RLE: `1RB1LB_1RC---_1LD1LF_1LE0LD_0LA1RF_1LC0RE`. The **previously known** BusyCoq `verify/Eqv_v2.v` theorem `TM2153.eqv` links that root's halting behavior to the auxiliary rooted RLE `1RB---_1LC1LF_1LD0LC_0LE1RF_1RA1LA_1LB0RD`. Agent12 independently simulated their complete physical-config merge at raw times 337226 (original) and 315075 (auxiliary); [existing source/provenance report](../agent12-r001-source/README.md). This invocation does not claim that equivalence or merge as new.

The auxiliary's sole undefined rule is A on input 1. **Our exact physical small-step table** in [Root119Gate.lean](Root119Gate.lean) implements all 12 auxiliary instructions on an arbitrary infinite `Int → Bool` tape, signed head, six named states, and authentic blank-A entry. `Reach` inductively records all successful raw instructions without a simulation bound.

## Quantified all-time result

`BB6Root119.blank_halts_iff_gate` proves the following equivalence **for the auxiliary machine's true blank start**:

```text
(∃c, Reach c ∧ next c = none)
↔
(∃d, Reach d ∧
     d.q = D ∧ d.tape d.h = 0 ∧
     d.tape(d.h−1) = 1 ∧ d.tape(d.h−2) = 1)
```

The proof is a complete predecessor classification: E is entered only from D reading 0; A is entered only from E; reading zero in E always returns A onto the zero just written in D; reading one in E puts A two cells left of D. Thus A/1 is reached precisely from a D/0 configuration with left cells 11. The reverse direction explicitly constructs both successful moves to the A/1 terminal query. `D_stop_after_two_moves` is a **universal arbitrary-tape lemma**, not a finite observation.

**Verified locally:** `lean Root119Gate.lean` using Lean 4.36.0-rc2. The kernel reports exactly `[propext, Quot.sound]` for the final theorem, no `sorryAx`, no `native_decide`, no imported axiom. The source code above is stand-alone and can be compiled independently. No upstream original-source CI is claimed.

## Independent computation, all checks finite

The independent [Node.js CommonJS test](test-root119-gate.cjs) directly parses all 12 RLE actions and independently implements the three-cell D/0 accelerated macro. It checks all 256 deterministic synthetic full-tape test cases and advances an authentic auxiliary blank-root tape for **2,000,000 successful physical instructions**, comparing raw vs macro state/head on *every* macro return and whole marked tape at 495 checkpoints plus the final configuration.

Output of the finite blank run:

- **1,983,313 macro calls** and 2,000,000 successful raw instructions.
- D/0 left-neighbor zero: **8,324** three-step macros, with A landing on the explicitly rewritten D cell.
- D/0 left-neighbor one and second-left zero: **19** three-step macros (first completed at raw time 1283).
- D/0 left-neighbor one and second-left one: **0** instances in the examined prefix.
- Final state F, head −296, 649 marked cells; no undefined instruction queried.

The finite trace cannot establish that the last category is empty forever. Tests must not be reported as additional theorems.

## Scientific scope and next obligation

This is an exact all-time **reduction of the genuine blank auxiliary halting problem to a localized physical tape pattern**. It does not classify that root or historical #119, prove any BB(6) value, or create a global BB(6) bound. The transition rule itself is elementary; external novelty has not been established, and an independent source-import verification remains desirable.

The decisive missing theorem is **`∀d, Reach d → ¬Gate d`** or a reachable gate witness, ideally from a closed symbolic language of genuine blank-origin D sections. A further reduction now exists below. A future guarded four-state B/C/D/F first-return map could collapse D→E→A into a three-instruction transition. It must preserve arbitrary outside tape and account for an undefined third query in the fatal case. Unrestricted fixed-head-window abstraction can synthesize false halts by forgetting previously visited cells; do not infer an inductive invariant from the finite observations.

## Further original-auxiliary all-time gate refinements (same invocation)

The separate [Root119CGate.lean](Root119CGate.lean), importing `Root119Gate`, proves `blank_halts_iff_C_gate` for **C reading 0** with the four physical cells immediately ending at its head equal to the word **1100**. The proof classifies the only two ways to enter D (C/0 or F/1); the F/1 transition writes zero at the immediate-left D cell and cannot satisfy the fatal D triple. Original table equality and reach semantics are unchanged.

The further [Root119BRegular.lean](Root119BRegular.lean), importing `Root119CGate`, proves `blank_halts_iff_regular_B_gate` for **a genuinely reached B/0** reading a left-to-right physical word belonging to

```text
11 00 (1 repeated r times) 0,   r ∈ ℕ
```

The rightmost 0 is under B. Precisely: at a reached B/0 head `h`, there is a finite `r` with all `t(h-1-i)=1` for `0≤i<r`, and `t(h-1-r)=t(h-2-r)=0`, `t(h-3-r)=t(h-4-r)=1`. The proof shows by induction that an arbitrary-length C/1 erasure sweep preserves every original tape cell at and left of its moving head. Its first C/0 encounter triggers the earlier C gate exactly when the B-origin word matches. Conversely every reached C/0 descends through finitely many C/1 sweeps from a reached B/0; a prior B/0 always exists because C is initially absent and can enter only from B/0 or C/1.

**Kernel checks:** `lean -o Root119Gate.olean Root119Gate.lean`, then `lean -o Root119CGate.olean Root119CGate.lean`, then `lean Root119BRegular.lean`, with the containing directory included in `LEAN_PATH`. All three compiled locally with Lean4.36.0-rc2. `#print axioms` on both additional final theorems returns exactly `[propext, Quot.sound]`; no `sorryAx`. These are stand-alone source-equation formalizations; the original external BusyCoq `TM2153.eqv` stays a separately published proof, with no kernel-level import bridge.

**Independent finite cross-check:** in 2,000,000 actual auxiliary instructions, the 8,189 visited B/0 sections have C-sweep one-run lengths `r=0:164`, `r=1:2592`, `r=3:5421`, `r=4:12`. None matches the fatal prefix `1100 1^r 0`. These distributions are empirical and make no claim of a closed all-time B language.

The remaining decision task is to prove the genuine B/0 language excludes `1100 1* 0` for **all** return times (or exhibit a reachable witness). Fixed finite memory around the head, or an enumeration of the 8,189 checked B sections, does not discharge it. The regular B-gate reduction is stronger as a *structural symbolic problem statement* but has no externally established research novelty or new BB(6) numerical bound. Keep intermediate classification.


## Independent 50-million-step falsification and a formal safety contract

The [bounded 50-million-step CommonJS single-file regression](test-root119-b-50m.cjs) parses all original auxiliary actions, runs on an independent typed-array full tape, and reports every genuine B/0 left-run length and four-cell boundary signature. The published script was reproduced independently with a separate C++ hard-coded-table interpreter at the same exact raw-step cap.

The **70,409** genuine B/0 sections observed through 50,000,000 raw steps have run-length counts:

| Consecutive ones immediately left of B/0 | Number |
| ---: | ---: |
| 0 | 558 |
| 1 | 22,583 |
| 2 | 9 |
| 3 | 47,226 |
| 4 | 33 |

The first **r=2** observation occurs after exactly **3,194,871 successful raw steps**, head coordinate −693, with the four-cell boundary after the 1-run equal to `0101`. **This refutes the provisional r∈{0,1,3,4} shortcut suggested by the first two million steps.** All 70,409 scanned B/0 boundaries avoid `0011` in order from closest-to-run outward, so none contains the fatal `1100 1^r 0` pattern. The 50-million-step completed state is F, head −3054. This is empirical reproducibility only.

A stronger **provisional genuine blank-orbit invariant**, suggested by the 50-million-step execution, is:

```
∀b, Reach b → BZero b → ¬HasLeft1100 b
```

where `HasLeft1100 b` means there exists any coordinate `x` such that the physical 4-cell word `1100` starts at `x`, ends strictly left of `b.h`, and is wholly before the live head. [Root119GlobalShield.lean](Root119GlobalShield.lean) proves, using the complete all-length B regular gate theorem, that **this exact premise implies nonhalting of the auxiliary blank-root machine**. The proof is local-kernel checked with only `[propext, Quot.sound]`. Crucially, the premise has **not** been proved and is not a result of the finite experiment.

[Root119FalseShield.lean](Root119FalseShield.lean) gives an explicit and **Lean-kernel-checked disproof of the tempting unrestricted-induction shortcut**. Define a synthetic initial B/0 state with head 0 and marked positions exactly `{-9,-8,-6,-5,-3}`. It has **no** `1100` anywhere to its left. After exactly **22 successful primitive steps**, it reaches B/0 with head 2 and marked positions exactly `{-9,-8,-5,-3,-1,0,1}`, which includes the physical `1100` factor at positions `-9,-8,-7,-6`. The original Lean module proves the input's full negative universal property and the output's positive witness, using `decide +kernel` for the exact 22-step computation. Final axiom audit `[propext, Quot.sound]`, no `sorryAx`. This synthetic state is **not claimed blank-reachable**. Thus a true-root proof requires a strengthened, history-sensitive language or a global invariant with additional conditions.

A separate 50-million-step state-sensitive scan also falsified the *overbroad* claim that all states avoid `1100` anywhere to the left; B/1, D/1, F/0 and F/1 do temporarily carry the pattern, while no B/0 in the checked prefix does. This observation helps constrain the shape of a useful inductive phase invariant. No globally closed grammar has yet been found.

## Proof build order

In the directory containing the six Lean files, using Lean 4.36.0-rc2 with `LEAN_PATH` set to that directory, build `Root119Gate.lean` then `Root119CGate.lean` then `Root119BRegular.lean` then `Root119GlobalShield.lean` as importable `.olean` modules (using `lean -o`). Compile `Root119FalseShield.lean` afterward. All five published modules have been successfully checked locally. This module chain establishes only source-equation mathematical results; source-original cross-proof-assistant connection and academic novelty remain separate.

Peer feedback was requested from Agent12, with explicit distinction from its published Eqv_v2 equivalent-root audit, in [the message](../../communications/agent12/2026-11-03T1238Z_agent42-root119-regular-gate-review.md).

**Proposed decisive next trial:** formulate a true blank-root B/0 regular language that implies the `HasLeft1100` exclusion and survives arbitrary genuine B-section returns. Stress-test it immediately against the 22-step synthetic counterexample and phase-dependent B/1/D/1/F features. No further blind raw-step extension should substitute for an induction.


## 2026-11-04: exact B/0 alternating sweep and suffix-shield preservation (Agent42)

[Root119BShift.lean](Root119BShift.lean) formalizes an exact **all-natural** (10n)-primitive-step macro. For every (n\in\mathbb N) and *arbitrary* two-sided exterior tape, if a B configuration scans 0 and has the immediate left suffix `(10)^n111` (written from far left toward its head), then `run (10*n) c = some (shiftMany n c)`. Each individual 10-step block shifts the B head left two cells, writing 1 at old offsets -4 and 0 and 0 at -2 and -1. The next B remains on 0 and retains suffix `111` until the n pairs are consumed. The proof uses induction on n and exact source-table transitions, with no global assumption about the actual blank orbit.

[Root119BShield.lean](Root119BShield.lean) adds a quantified preservation statement. `NoLeft4 p q r c` means no factor `p q r 0` lies *entirely left of the head*. For **any** three Boolean bits p,q,r, every such 10-step sweep preserves this property, since the only possibly new four-letter windows entirely left of the new B head both end in 1. `reached_sweep_preserves_noLeft4` also proves that if the starting configuration is genuinely `Reach`-reachable from blank, the macro endpoint is `Reach`-reachable under the exact original source-step semantics. The family includes the observed dangerous B-gate factor `1100`, plus `1000` and `1110`.

**Source-original manual CI passed:**
- [41777338183](https://github.com/FlareZ123/bb6/actions/runs/41777338183), source import `Root119Gate` and proof `ten_n_steps`;
- [41777783148](https://github.com/FlareZ123/bb6/actions/runs/41777783148), unchanged original imported source, full `Root119BShift` and `Root119BShield` with all theorem axiom audits exactly `[propext, Quot.sound]`, no `sorryAx`.

Both verifications used Lean 4.36.0-rc2 on manual workflow [agent42-root119-bshift.yml](../../.github/workflows/agent42-root119-bshift.yml). Local derivation was independently checked in a minimal literal transcribed table before source compilation. This is an **intermediate conditional transition and invariant-preservation theorem**, not an all-time global invariant: actual blank-root B/0 configurations can enter other return mechanisms, especially when the left prefix no longer matches a `10` pair. Previously documented synthetic B/0 counterexamples remain decisive against unrestricted closure. **Root119's actual blank halting status and BB(6) are still undetermined.**

**Next direct target:** prove a source-sound return-and-shield lemma for the exceptional B/0 boundary with left `0000 111`, or find a concrete counterexample. Early blank-root trace at raw time 73 demonstrates a 16-step expansion to a B/0 beyond a fresh zero region (raw time 89). Treat this as a finite lead until a universal source theorem and genuinely linked return-language argument exist.


## 2026-11-05: rightward D/F all-length source-table identity and conditional 1100 shield (Agent42)

[Root119DFSweep.lean](Root119DFSweep.lean) proves the exact *rightward* D/F phase, complementary to the already-verified leftward B expansion in [Root119BFull.lean](Root119BFull.lean) and [Root119BFullShield.lean](Root119BFullShield.lean). It uses the same physical `Int → Bool` tape and twelve original auxiliary table instructions, imported via `Root119BShield`. This is an intermediate all-natural identity, not a root decision.

For any D-state configuration whose consecutive pairs of cells at positions `h+2i,h+2i+1` are all 1 for `0≤i<n`, the exact `2n)-primitive-step computation reaches state D at `h+2n`, having rewritten precisely the odd cells `h+1,h+3,...,h+2n−1` to 0, with all other cells unchanged. The recursive canonical full-configuration map is `dfMany n`; theorem `df_two_n` certifies the exact equality, with arbitrary untouched exterior.

Theorem `df_pair_preserves_1100` proves a two-step D/1,F/1 pair cannot introduce any all-left factor `p q 0 0` if absent before the pair, for arbitrary `p,q`. Inductively, `df_many_preserves_1100` transfers this property through every valid `n)-pair sweep. `reached_df_sweep_1100` composes exact `Reach` preservation with the `1100` instance for genuine blank-reachable *starting* D-phase configurations satisfying the shield. The shield assumption at the D-entry is essential and is **not** universally true of genuine reached D states.

Local Lean 4.36.0-rc2 kernel compilation succeeded with `#print axioms BB6Root119.reached_df_sweep_1100` reporting exactly `[propext, Quot.sound]`, with no sorry. That preliminary local compilation used literal-machine, interface-identical stand-ins for upstream `Root119Gate/Root119BShift/Root119BShield`. Manual original-module CI workflow [agent42-root119-dfsweep.yml](../../.github/workflows/agent42-root119-dfsweep.yml) was dispatched as [run 41960795579](https://github.com/FlareZ123/bb6/actions/runs/41960795579); **original-import CI remains pending** at this writing. Do not promote as source-original checked until that run succeeds and axiom audit is inspected.

Distinctness check: earlier `Root119BFullShield` already covered the B-phase left 10n+16 return, so an initially constructed separate 16-step expansion file was removed as redundant (Git commits c6dc07b and 8bc7340). The new D/F proof handles the complementary rightward phase and has no universal starting invariant. The next genuine-root obligation is a phase-sensitive return-language invariant, including branches that temporarily create `1100` outside B/0. A new independent bounded trace through 10,000,000 raw instructions found the first left `1100` during a genuine D/1 phase at raw step **3,194,059**, head **−691**, pattern starting at **−695**; subsequent B/0 sections remained safe in this bounded scan. This observation is computational only and warns against applying the D/F shield without checking its premise.


**Source-check update, 2026-11-05 03:21:30 UTC:** The previously pending manual CI [41960795579](https://github.com/FlareZ123/bb6/actions/runs/41960795579), exact commit `a62fd6ebe3c56efaba4feef57256b66d709a63a9`, has **succeeded**. Job `df-sweep` [127026422135](https://github.com/FlareZ123/bb6/actions/runs/41960795579/job/127026422135) rebuilt unchanged repository modules `Root119Gate`, `Root119BShift`, `Root119BShield`, then compiled original-import `Root119DFSweep.lean`. Job logs display `#print axioms` for all three final theorems as exactly `[propext, Quot.sound]`, without `sorryAx`. This supersedes the provisional source-check status above. The source is still a literal standalone translation of the published auxiliary machine; original external Coq-to-Lean `TM2153.eqv` transport and genuinely-rooted global shield remain separate obligations.



## 2026-11-05: arbitrary-length F/1 forward-and-back wave with one-bit normal form

The complementary all-length `F/0→B/1→F/0` two-step retreat is proved in [Root119FBSweep.lean](Root119FBSweep.lean). Theorem `fb_two_n` preserves arbitrary physical exterior tape, `fb_many_preserves_noLeft4` preserves *every* left four-word ban during these leftward sweeps, and `reached_fb_sweep_safe` transports blank-auxiliary reachability. **Original-module Lean CI [41961744091](https://github.com/FlareZ123/bb6/actions/runs/41961744091) succeeded.**

A much more useful composition, proved locally in **[Root119Wave.lean.xz.b64](Root119Wave.lean.xz.b64)** (LZMA-compressed base64 UTF-8 Lean source), combines the `F/1→D` initial step, the `2n)-step D/F forward erasure, the far-end `D/1→F/0` reversal, the `2(n+1))-step F/B backward restoration, and the final `F/0→B/0` step. This proves the exact `4n+5)-instruction return, on *arbitrary tape outside the stated finite corridor*. `wave_full_preserves_noLeft4` proves every forbidden four-word to the left of an initial F/1 head remains forbidden at the returned B/0 head, even if it appears transiently during the forward pass. `reached_wave_safe` combines the conditional return, blank-auxiliary reachability, and the `1100` shield.

[Root119WaveNormal.lean](Root119WaveNormal.lean) strengthens the theorem to the following explicit **entire-tape identity** (`wave_explicit`), with no recursive phase terms in the conclusion:

Let `c.q = F` at `h`, and assume `t(h)=1`, `t(h−1)=0`, `t(h+i)=1` for every `1≤i≤2n+1`, and `t(h+2n+2)=0`. Then

`run (4n+5) c = some ⟨B,h−1,setBit t (h+2n+2) true⟩`.

So the wave writes exactly **one net new 1**, at the rightmost sentinel zero, while returning to a B/0 one cell left of the original F/1. This is a genuine all-natural mathematical statement and is stronger than a finite simulation. The full-tape proof uses `df_many_unvisited`, `fb_many_unvisited`, the written-cell formula, and a tape extensionality argument. Its `#print axioms` locally reports `[propext, Classical.choice, Quot.sound]` with no `sorryAx`; the source-original CI is described below.

**Reproduction:** Decode `Root119Wave.lean.xz.b64` by base64 followed by LZMA/XZ into `Root119Wave.lean`; SHA-256 of the decoded source must be `715e5512da53986da896ea05d68d28869fc8489b6ad3e1e49e26459545299930` (13,570 bytes). The manual source-original CI [workflow](../../.github/workflows/agent42-root119-dfsweep.yml) performs this decode, checks the SHA-256, builds the unchanged original `Root119Gate`, `Root119BShift`, and `Root119BShield` plus new D/F and F/B modules, then checks both the wave and normalized theorem in Lean 4.36.0-rc2. Runs [41962705131](https://github.com/FlareZ123/bb6/actions/runs/41962705131), [41963352251](https://github.com/FlareZ123/bb6/actions/runs/41963352251), and subsequent dispatch on final `wave_explicit` source were pending or in progress when initially written; **source-original all-wave status must be confirmed from the final run**.

The independent CommonJS regression [test-root119-wave.cjs](test-root119-wave.cjs) checks 390 seeded exterior tapes across lengths `n=0..12` and a separately reached auxiliary blank-tape witness. At exact raw time **3,194,058**, the true auxiliary blank execution has F/1 at head **−692** with `n=202`; after **813** steps (time **3,194,871**), it returns B/0 at **−693**. The *only* net tape change is cell **−286** from 0 to 1. The preceding F1 step creates the first observed temporary all-left `1100` factor at D/1 raw time 3,194,059, and the wave removes it before B/0. This is a concrete example of why single-state shield induction fails but full-phase return induction can succeed. The 390 synthetic and one authentic witnesses are empirical checks of a mathematically quantified theorem.

**Boundary of achievement:** The hypotheses constrain a particular F/1 corridor and an existing F-entry shield; neither that corridor nor that shield has been proved for every blank-reachable return. Other B/0 return branches remain. No BB(6) exact value, universal upper bound, or universal root119 nonhalting proof is claimed. This work belongs in `im-results/` until a genuinely frontier-changing root theorem is proved.


## 2026-11-07: exact even and odd-even B/0 prefix returns (Agent42)

The new [Root119OddEvenChain.lean](Root119OddEvenChain.lean) proves two source-original conditional first-return laws, using the already source-verified odd F/1 wave theorem and a new exact even D-sweep return lemma.

For a reached B/0 configuration at head \(h\), assume the immediate left cells are \(1,0,1\). Define \(m\) to be one plus the maximal consecutive right-hand run of ones starting at \(h+1\).

1. **Even family.** If \(m=2n+2\), the right block \(h+1,\ldots,h+2n+1\) is all ones and the two cells \(h+2n+2,h+2n+3\) are zero. The exact return time is \(m+13=2n+15\), with returned B/0 head \(h+m+1\).
2. **Odd-even family.** If \(m=2n+1\), the right block \(h+1,\ldots,h+2n\) is all ones and the three cells \(h+2n+1,h+2n+2,h+2n+3\) are zero. The exact return time is \(3m+20=6n+23\), with returned B/0 head \(h+m+2\).

The common prefix is a nine-step B/0-to-F/1 transition. In the even family, the F/1 phase is followed by an even D sweep. In the odd-even family, it is followed by the already proven odd F/1 wave, a B/1-to-F/1 transition, and an even D sweep. The new lemma evenSweep_to_B_exact gives the full resulting tape for an arbitrary exterior tape, not merely the returned state. Both return theorems preserve Reach and end in BZero.

**Source-original CI passed:** manual workflow [42405102264](https://github.com/FlareZ123/bb6/actions/runs/42405102264), commit beecb292363ed7f024c1ac969701915249a28f74, Lean 4.36.0-rc2. The dependency closure was rebuilt from source. The axiom output was:
- evenSweep_to_B_exact: [propext, Classical.choice, Quot.sound];
- b0_even_prefix_to_b0: [propext, Classical.choice, Quot.sound];
- b0_odd_even_chain_to_b0: [propext, Classical.choice, Quot.sound];
- the nine-step b0_two_wave_prefix: [propext, Quot.sound].
No relevant theorem depends on sorryAx. The direct-even proof was also checked in a local Lean 4.36.0-rc2 model before the source-import run.

The independent Node.js replay [test-root119-two-wave-census.cjs](test-root119-two-wave-census.cjs) simulated 10,000,000 raw steps and observed 22,984 B/0 configurations, hence 22,983 consecutive B/0 intervals. The complete checked first-return class vector was:
- ten-step: 15,176;
- existing odd-wave: 7,508;
- existing left-one-wave: 177;
- new even-prefix: 21;
- new odd-even-prefix: 22;
- unmatched left-prefix candidates: 8;
- other: 71.

All 43 new-family predictions matched the raw replay in both time and returned head. This is finite census evidence; the Lean theorems are conditional statements for all natural parameters and arbitrary exterior tape, while the census only demonstrates that their hypotheses occur 43 times in this finite segment.

The eight unmatched left-prefix candidates fit the observed two-wave-root formula \(8n_1+2r+30\), with head displacement \(-2r-6\), for parameter pairs \((n_1,r)=(6,15),(1,17),(2,46),(4,2),(5,109),(7,73),(8,194),(3,1)\). This correspondence is currently computational only: the separate Root119TwoWaveRootPrefix.lean file fails source compilation in its D-retreat shield proof and is not an importable dependency. A broadcast and a correction at the top of this directory's README flag that status.

**Limits:** the two new return theorems do not yet prove transport of NoLeft4 through every intermediate state. The 8 two-wave candidates remain unverified at source level, and 71 intervals remain in the census's other class. The next useful work is to prove shield preservation for the new macros and classify further B/0 prefixes. These results do not determine BB(6) and do not establish a universal upper bound.
