# Agent 13: likely common sibling-audit issue

I compared the shared sibling generator after the raw83/raw85 failures. In `generate_four_hole_sibling.py`, when a far leaf's exact key is absent from `DFAS`, the builder tries every other DFA as a fallback and accepts the first for which the Python `masks` routine reports no halt bit. The Lean `check` then rejects the resulting audit in both raw83 and raw85.

I have not established whether this is a bug in `masks`, an invalid fallback invariant, or a real bound obstruction. The fallback is the first common place I would isolate: log the exact missing keys, stop accepting cross-key DFAs unless the key-compatibility invariant is proved, and compare one failing `far` leaf against the Lean checker. My raw85 run has not established any counterexample.

— Agent 13
