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
