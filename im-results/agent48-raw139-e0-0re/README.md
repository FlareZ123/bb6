# Raw139 E0=0RE: complete computational candidate at weighted bound 852

Exact parent `[7,24,11,24,14,24,24,16,17,11,24,24]` (A0,A1,...,F0,F1; code 4q+2w+d; 24 unassigned). This is a distinct six-hole depth-two sibling, not any C1, D0 or F1 descendant.

A first-hole census with translated cycles through 450 steps and ordinary FAR d≤2 produced 11,690 internal splits, 216,456 cycle leaves, 41,263 last-hole leaves, 10,416 FAR leaves and 736 open leaves. The maximum first-hole time in the census was 193. All 736 opens have now been classified computationally: 734 Block-FAR certificates (widths 2/3), one final hole F0 at step 846, and the exact inductive sweep below. Candidate weighted bound 852 = 846+6. No original-source accepted parent Cover yet.

## Exact symbolic last leaf

Table `[7,21,11,24,14,23,3,16,17,11,15,20]` has only B1 unassigned. With the head-inclusive reverse-left zipper, let X(n,k,h) be state A at h, left [0,1,1], right 0^4 1^(4n) 0^k, both sides zero padded. Blank enters X(0,17,-4) at step 636.

The exact recurrence is X(n,k,h) → X(n+1,max(k−3,0),h−1) in 20n+75 steps. Its decomposition: 26 preparation steps; 2n right-moving pair macros of four steps; five turning steps; 4n+8 left-moving one-symbol macros of three steps; 20 finishing steps. All these macros preserve arbitrary untouched tails. Iteration yields an unbounded live run independently of B1. In particular after j complete cycles the elapsed step count is 636+10j²+65j.

The computational definitions and proofs of SparseZipper.move/step/zrun, join and zrun_shift were copied exactly into a local Lean 4.36.0-rc2 preflight. All growth, seed and arbitraryRun theorems passed with [propext, Quot.sound] only (seed propext). The actual-source bridge `never` is included in E0ZeroRESweep.lean, awaiting an original-source audit. This is real all-time progress, not a claim that a long simulation constitutes a proof.

The complete parent candidate is under construction; all numerical witnesses still require the original checker. A concise reproduction spec and scalable certificate generator are the next checkpoint.
