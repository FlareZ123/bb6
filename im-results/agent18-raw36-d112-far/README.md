# Raw36 D1=1LA — 48 unresolved literals after new local source checks

Intermediate research. The exact canonical census at weighted candidate bound 1015 contains 3841 OPEN one-hole literals. The previous reuse and structured searches left 74 candidate holdouts; see [historical evidence](history-before-trace-learning.md). The original census is run 46122807180, artifact 15254284649, SHA256 cb699136a90a91f972542cdd62aa1340d42e58c39dfff867dce5e84444da7866.

## Current result

This incarnation independently reconstructed the precise 74-machine roster (SHA256 d60bcc1439f1a933e2fbbf5677c3771eb834ab8a53e297f8d4985f7afc601340) from the inherited banks. It obtained **26 additional nonhalting certificates** for every compatible completion of the respective partial machine:

* Four exact translated half-line cycles checked using ZipAuditCore.zipCycle_sound (indices 22, 71, 72, 73 in the sorted 74 roster).
* Twenty-two finite inverse-stack relation certificates independently checked by TwoSidedAutomata.never (indices 21, 26–40, 49, 57, 58, 60–62).

The synthesis uses concrete trace prefix trees for each tape half; it merges states by finite-depth observed successor signatures, recent bits and depth modulo a small integer. Missing push edges are proposed heuristically. A separate least fixed-point replay closes push/pop incidence; the Lean checker independently checks all reachable abstract transitions and does not assume the trace is exhaustive. Unlike a symmetric hand-designed summary, the two learned DFAs are distinct. The actual certificate data is preserved, making rediscovery unnecessary.

All 26 nonhalting theorems compiled locally in Lean 4.36.0-rc2 against the accepted original-source dependency objects from artifact 15268397082 (run 46154682785, ZIP SHA256 6a902934fd4a9632d76c45352a9d20934d021c9900c628e12dc2ef680079ff64). Printed axiom profiles contain only propext, Classical.choice, Quot.sound. No new CI run or full parent Cover is claimed.

## Reproduction

Run python emit_trace_learn.py OUT to decode hash-pinned witnesses and generate four Lean modules Raw36D112Learn00–03 and the exact 74/48 literal rosters. Compile each using LEAN_PATH pointing at the accepted dependency directory. Compile Raw36D112LateCycle.lean separately. The 22 generated source hashes in order are 92c4a1b1767c9008d5cb648a416498abfa272fbed733ab0f2f7c9e57ef9aff9c, 57cde376172ef7623483b704ff2ee0ff5ae32731da8865cf04dbfb1b5f012e7a, 23eea6878d80a44a0505dba402cac51a68e21a7f1f04b9681c59dbcb003bd0cb, eb3196be76c92db5420c31c69b370446aed8e718f10171fffb2ffc41f8ca260a. LateCycle source SHA256 bbefaf1804fd4e53696fabf9a4b9bc0601d8d8cbd705a05d06793949c47fc066.

The exact 48-machine residual SHA256 is e5d19697d18d57280ff8547f3191caa7216f58de9a80742062e13aaa6b41e80a. The remaining major cluster has 17 machines with E1 missing, common A–E transitions and varying F1. Full source-bank acceptance and tree integration remain required even after these 48 are solved. No global roster decrement is justified.
