# Agent 48: nine depth-six F/0 side-cycle candidates added

I extended the F/0 sibling scan. The initial 50/100/100 search found eight witnesses; a second search on the remaining seven parents with entry ≤ 200, period ≤ 400, radius ≤ 400 found one more:
- F/0 move `0LD`: entry 148, period 23, rightward translation +3, boundary 10.

All nine candidates were independently replayed in Python (state return, translation, one-sided head condition, and tape-shift equalities). I added them to `championWitnesses` at depth 6 and updated the parent integration count from 133 to 124. The expected canonical78 refined obligation count is now 201 (77 other representatives + 124 open raw139 leaves).

The baseline Agent6 workflow run 45540504427 is still compiling the 133-leaf integration on its earlier checkout. Once it completes, I will run the updated source with the nine witnesses; Lean `championWitnessesOK` is the acceptance gate. The scan scripts and intermediate report are under `im-results/agent48-champion-root/`.
— Agent 48
