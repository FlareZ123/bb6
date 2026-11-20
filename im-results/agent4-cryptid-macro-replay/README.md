# External A-macro replay and first DRegular checkpoint

**Status:** independent, reproducible macro replay plus a Lean-checked arithmetic bridge. This is not a blank-root halt proof and does not solve BB(6).

## Pinned target and source

The external Lean proof is pinned at commit **1929f57df4dd7afcc11c3f458e20526fd1f991e0**, file:

**BusyLean/Individual/1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---.lean**

It starts from the halting cylinder **A(3^108*k + C, [])**, where

**C = 1975700577069254261393123959451562008800234946348086**.

The proof applies 107 A_step2 macros (ten groups of ten, then seven), followed by its final finish proof. The complete argument list, each intermediate A-section, and the checkpoint assertions are preserved in [macro_trace.json](macro_trace.json).

## Independent replay

[cryptid_A_step2_replay.py](cryptid_A_step2_replay.py) reconstructs each macro invocation from the exact post-step_An_1101 configuration:

1. Build the A/E/B intermediate tape, including the reversed ListBlank orientation of the alternating left block.
2. Execute exactly the literal m raw transitions using the six-state transition table.
3. Check the C-state and alternating-block precondition for step_01C_C11, including the two leading context ones.
4. Apply the long step_01C_C11 sweep algebraically, then the final two raw transitions, to compute the next A(n,r).
5. Preserve the represented right-list extent, including trailing blank zeros. Dropping those zeros makes several exact checkpoint lists disagree even though their infinite tapes agree.

**All 11 explicit external checkpoints match exactly:** after 10, 20, 30, 40, 50, 60, 70, 80, 90, 100, and 107 macros. Both the enormous unary parameter and the complete suffix list match. This is an independent computational replay, not a replacement for the external kernel proof.

Across the 107 A_step2 invocations the intermediate step_An_1101 branch counts are 52 E and 55 B, with no A branch. The final input to finish has parameter congruent to 1 mod 3, so its final branch is E: 53 E and 55 B in total.

## Exact first-ten DRegular bridge

The first ten external macro calls have arguments:

**13, 21, 5, 5, 21, 5, 17, 21, 5, 27**.

Their regular-suffix transitions are:

| Call | DRegular case | Input (q,b) | Output (q,b) | A_step2 argument |
|---:|---|---:|---:|---:|
| 1 | E0 | (0,0) | (1,5) | 13 |
| 2 | Ege3 | (1,5) | (3,2) | 21 |
| 3 | Bq | (3,2) | (2,2) | 5 |
| 4 | Bq | (2,2) | (1,2) | 5 |
| 5 | E2 | (1,2) | (2,0) | 21 |
| 6 | Bq | (2,0) | (1,0) | 5 |
| 7 | Eempty | (1,0) | (1,7) | 17 |
| 8 | Ege3 | (1,7) | (3,4) | 21 |
| 9 | Bq | (3,4) | (2,4) | 5 |
| 10 | Ege3 | (2,4) | (4,1) | 27 |

At individual steps the represented suffix list can carry a trailing blank zero; the ListBlank section interpretation ignores that terminal blank. The ten-step checkpoint suffix itself is exactly (01)^4 1.

The first ten calls take **A(3^108*k+C, [])** to

**A(3^98*(8^10*k)+D1, [0,1,0,1,0,1,0,1,1])**,

where

**D1 = 35925965576050291197954676646168812866911688985763244505**.

The corresponding DRegular checkpoint is **DRegular.run 10 ⟨D1,4,1⟩**. More precisely, [First10AffineBridge.lean](First10AffineBridge.lean) proves, for every natural k:

    DRegular.run 10 ⟨3^108*k + C, 0, 0⟩ =
      some ⟨3^98*(8^10*k) + D1, 4, 1⟩

The base ten-step computation is closed by decide; the affine lift uses the existing BB6.DRegularShift.run_shift theorem and the identity 3^108 = 3^10 * 3^98. It was compiled locally with Lean 4.36.0-rc2. Its axiom report contains no sorryAx; the affine theorem inherits only the standard [propext, Classical.choice, Quot.sound] profile of the existing shift theorem.

This is an arithmetic-model theorem. The existing DRegularSourceShift and ARegular3AdicBridge developments provide the relevant original-source transport and physical-section encoding; this invocation did not recompile their full dependency closure.

## First nonregular handoff

At the end of macro 10 the external path is at **L(D1,4,1)**, suffix **(01)^4 1**. Macro 11 is **A_step2 35**. The DRegular table has no regular successor for the E case q=4,b=1, but the external macro continues to

**A(95802574869467443194545804389783500978431170628701985341, [0,1,1,1,1,1,1,1,1,0,1,1,1,1,1,1])**.

The next ten macros reach the exact external checkpoint

**A(3^88*(8^20*k)+D2, [0,1,0,1,1,1,0,1,0,1,0,1,1,1])**,

where

**D2 = 653274599173389056319717515476765122857837155218448003942322**.

That suffix 01011101010111 is outside (01)^q1^b. Agent 2's existing q=4 E/E plus P2 source closure is a later regular return, not the next external A-macro transition. The trace preserves the intervening arbitrary-suffix states rather than skipping them.

## Research consequence and boundary

The external halting cylinder is formally proved to halt. This replay independently reconstructs its 107 A-macro transitions and identifies the exact first-ten DRegular checkpoint and first suffix escape. It does **not** show that the authentic normalized blank-start orbit **A(9,[])** reaches **A(3^108*k+C,[])**, or any other certified halting class.

The remaining BB(6) problem is to source-certify the arbitrary-suffix transitions/reentries and, ultimately, connect the genuine blank-start orbit to a halting cylinder. Do not treat a finite return chain, a DRegular arithmetic path, or this external-cylinder replay as blank-root reachability or as a nonhalting proof.

## Reproduction

Run the Python replay and Lean theorem with the repository's archived DRegular source and the existing DRegularShift module:

    PATH=/tmp/lean/lean-4.36.0-rc2-linux/bin:$PATH ./im-results/agent4-cryptid-macro-replay/reproduce.sh

The script writes/refreshes macro_trace.json. Set LEAN to another Lean 4.36.0-rc2 executable if needed.
