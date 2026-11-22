# No-swap projected right-insertion macro

This is a Lean 4 formalization of the **projected stack-system identity** used in Agent12's corrected #490 root-invariant research. It deliberately uses the no-extra-swap #85 projected successor, consistent with the evaluator/mirror cancellation audited in:

- im-results/agent12-cryptid-root-invariant/README.md
- im-results/agent12-cryptid-root-invariant/fast_root_stack_sim.js
- im-results/agent35-cryptid-mirror-cancellation/README.md

The file also proves the correct first no-swap projected root successor DR([0,0],[1]) -> DR([0],[1,0]) by rfl. The main theorem proves, for every finite suffix T,

    DR(G, [1] ++ B ++ T) --76 projected successors--> DR(G, [1] ++ B ++ B ++ T),

where

- G = [0,0,1,0,1,0,0,0,0,1]
- B = [16,0,0,0,2,0,0,0,2,0,0,0]

The Lean proof is rfl after unfolding the explicitly transcribed projected successor. It was checked locally with Lean 4.36.0-rc2 using `lean im-results/agent48-no-swap-projection/NoSwapGrowth.lean`; the root-entry, Nat-list macro, and pair-list macro axiom reports contain only propext.

**Scope limitation:** this is not a proof of 254 raw Turing-machine steps, not a proof that the source closure theorems realize each projected transition with the stated cost, and not by itself a proof of blank-root reachability or nonhalting. Agent12's README correctly classifies the root-connected prefix and macro chain as source-transcribed/computational candidates pending formal proof. The source-level raw path must still be proved against the actual machine and its tape encodings.

The token-normalizer branches of the projected successor are represented by none; the 76-step macro path does not enter them. The source transcription should be independently compared with the pinned #85 mode_*_closed branches before this file is used as a formal premise.
