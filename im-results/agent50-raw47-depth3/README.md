# Raw47: complete exact weighted parent closure

**Parent:** `1RB---_1RC---_0RD---_1LD0RC_------_------` (seven holes; `25^7 = 6,103,515,625` physical total completions).

## Source-accepted theorem and status

**All 1,212 depth-three quotient residuals are closed.** The original source proof accepted by Lean 4.36.0-rc2 establishes the exact local **weighted** maximum **143,977**:

- `BB6.Agent50Raw47Complete.cover : Cover (WeightedBound 143977) parent`
- `BB6.Agent50Raw47Complete.all_quotient`: equivalent bound over quotient-compatible machines;
- `BB6.Agent50Raw47Complete.exact_threshold`: for every `B`, all compatible completions satisfy `WeightedBound B` **if and only if** `143977 ≤ B`.

The final source closure and theorem/axiom audit passed [GitHub Actions run 46068688341](https://github.com/FlareZ123/bb6/actions/runs/46068688341), source SHA `5bd193066b82be12e3fa5e1e74477a3ff3ca5193`. Its `raw47-lifted1212` artifact is **15232511020**, archive SHA-256 `bfb3faae9359044ae0ebf1c233ec23f68d63cfee18e19dfb8db8cd584ca479c8`. Exported theorems passed an axiom audit permitting only `propext`, `Classical.choice`, and `Quot.sound`; no admitted proofs are used.

This is a genuine exact weighted maximum **for Raw47**, not the exact value of BB(6). The current accepted global conditional interface remains Canonical41; Raw47's unique membership and actual representative removal must be accepted separately. The prepared [Canonical41 consumer](../agent50-raw47-canonical41/consume.py) was dispatched in [run 46069652144](https://github.com/FlareZ123/bb6/actions/runs/46069652144), and cannot be described as accepted until that run passes.

## Proof decomposition

The original depth-three quotient tree has 126 first-hole splits, 1,567 cycle closures, 120 state-introduction aliases, and **1,212 distinct canonical residuals**. The source-accepted low-threshold consumer `BB6.Agent50Raw47Accepted1211` closes **1,211** of them at `WeightedBound 10006`, and kernel-checks that exactly one representative remains. This passed [run 46056674185](https://github.com/FlareZ123/bb6/actions/runs/46056674185) with `raw47-accepted1211` artifact 15226844140 (SHA-256 `f212fa5d6ca37857d5efe3a7c877ced0cae6d7d367d00c08dcdfbf88dee430d9`).

The sole exceptional remaining residual is index **61**, table `1RB1LA_1RC---_0RD0LE_1LD0RC_0LA---_------`. Its hard last-hole completion `1RB1LA_1RC0LF_0RD0LE_1LD0RC_0LA0RB_---1LB` reaches its undefined slot after **143,975** ordinary moves. [`CheckedSweepTrace.lean`](CheckedSweepTrace.lean) checks the exact universal block-transfer rules; the generated trace uses **2,741 commands** in 69 chunks. A halting completion has incoming blank delay **1**, giving the sharp weighted score `143975 + 1 + 1 = 143977`. The exceptional parent bound and attainment passed [run 46033320715](https://github.com/FlareZ123/bb6/actions/runs/46033320715) (artifact 15215900592). See [Late61.md](Late61.md).

The lifted `Raw47Lifted1212.remaining_count` theorem checks that filtering this single certified parent produces an *empty* residual list. `Raw47Lifted1212.local_sound`, [`Raw47CoverEmpty.lean`](Raw47CoverEmpty.lean) and the source [`Raw47Complete.template`](Raw47Complete.template) transfer the 1,211 bounded branches plus parent61 to a complete parent Cover, while [`Raw47Attainment.lean`](Raw47Attainment.lean) supplies the lower bound.

## Reproduction and scope

Run the existing manual workflow [`agent50-raw47-lifted.yml`](../../.github/workflows/agent50-raw47-lifted.yml) with `mode=lift`, `base_run=46056674185`, `base_count=1211`, `late_run=46033320715`. It retrieves the pinned accepted proofs, verifies source and object compatibility, compiles `Raw47Complete`, checks its theorem and axiom profiles and exports the source manifest and Lean objects. The exact published result and caveats are recorded in [the mathematical result](../../results/2026-11-27-raw47-exact-weighted-maximum-agent50.md).

## Historical accepted cuts and methods

Accepted807 (405 open) followed accepted766, 729, 702, 678, 168, 120, and 108. All 674 pure FAR parents and the 23 pump/counter parents were consumed before accepted702; the subsequent exact graph batches add more parent Covers. The cap-10,000 scan produced 45,817 open leaves; FAR through five states closes 43,659 candidates, n-grams widths 2–10 close 1,498 (544 overlap). With the original hard-leaf theorems this left 1,192 candidate leaves across 382 parents. Agent12 run-graph search and Agent2 carry proofs discharge the rest; only exact parent audits and source-accepted composition count as proof. See [PumpCertificates.md](PumpCertificates.md), [CounterCertificates.md](CounterCertificates.md), and [Late61.md](Late61.md).

## Historical experiments

The verified depth-2 Raw47 cut leaves 114 five-hole residuals, none certified by FAR through six states. This experiment increases the local split depth from 2 to 3 while keeping the same 1,000-step simulation cap and 32-frame cycle lookback. It then runs the FAR5 bank over every resulting open residual.

Reproduce with `.github/workflows/agent50-raw47-depth3.yml` or `bash im-results/agent50-raw47-depth3/run_depth3.sh [output-directory]`.

The purpose is to expose one more undefined transition per surviving branch. Open leaves may therefore have four or five holes depending on whether a branch reaches the simulation cap before the next split. The output records the exact tree, open list, FAR5 candidates, and hole-count distribution.

This is intermediate computational evidence. A candidate bank is not a proof until converted into Lean FAR certificates and checked; a deeper tree does not by itself reduce the global Canonical64 obligation count.
## FAR6 preloader correction

The first FAR6 attempt was invalid: the C++ preloader expects one bare code token per line, but the initial runner passed the FAR5 `id code` output. It therefore parsed IDs as automaton codes and falsely reported all 1212 leaves solved in 0.00 seconds. Those files are explicitly preserved with an `-invalid` suffix. The corrected runner extracts only the second column of the FAR5 bank, validates the ten bare codes, and reruns FAR6. Only the corrected run may be cited.


The prior `raw47-depth3-far6.txt` is invalid (contains numeric IDs treated as codes). Do not use it as evidence.
