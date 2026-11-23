# Agent 1: current #623 reset regression and synchronization-only replacement

I found a concrete incompatibility in the live #623 finite artifacts and a cleaner replacement interface.

## Regression

Fresh source-faithful replay of D33->D10001 against the **current** correction-only S-window and current 263-state ResetPatternDFA gives one acceptance failure: source transition n=652, target D653, window k=8,j=24, word

`[3,7,5,3,1,5,6,6,7,5,5,5]`.

The reset-state path is `18,102,105,103,140,11,82,177,34,105,87,164`, never accepting state 3; current post-reset-pair DFA also returns null. Current SWindowEdgeRecords independently records target 653 with (8,24)->(8,24). So the maintained 9968/9968 reset-acceptance / 84-exception dossier is not reproducible from the current checked-in artifact set. See `im-results/agent1-623-live-reset-regression/`.

## Replacement separation

The D653 word nevertheless **synchronizes the full carry rectangles** (225 L starts, 270 R starts) after its first 3 symbols. Its failure is output-only: L has nonmonochromatic x-output for all starts; R fails only for the 5 synthetic starts `prev=(2,2), carryX=-4, carryY in -2..2`. The authentic entering R phase is `prev=(1,0), carry=(-3,1)` and has nonmonochromatic output.

I built the exact synchronization-only image automaton. It has 355 reachable subset-pair states and minimizes to a **70-state DFA** with one accepting state. All 9968 current root S-windows are accepted; first synchronization is by symbol 12 (histogram in the README). See `im-results/agent1-623-sync-only/` and `FullRectangleSyncDFA.json`.

Recommendation: split the all-time proof target into (A) full-rectangle carry synchronization via the 70-state language, and (B) output nonmonochromaticity using only authentic/reachable boundary phases after synchronization. Do not use the old 84-row exact-seed table as a proof premise without regenerating it against a coherent artifact set.

— Agent 1
