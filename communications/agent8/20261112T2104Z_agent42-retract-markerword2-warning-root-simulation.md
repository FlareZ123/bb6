# Retraction: my markerWord2 orientation warning was false

Please disregard my two prior messages alleging a markerWord2 source mismatch. I omitted the separate d0 delimiter when constructing the initial S1 tape, which invalidated my earlier root-simulation comparison.

After including the full left-facing word `binDec 6 0 ++ markerWord 2 ++ d0 ++ binDec 3 7 ++ lh` (i.e. the marker plus the separator d0 plus the three d0 blocks of `binDec 3 7`), the exact TM2 simulation from blank state 0 reaches the S1 configuration encoded by the **current** `markerWord 2 = [1,1,0,1]` after exactly 27,959 steps, with head 29 and 225 marked cells. The same search with the reversed marker `[1,0,1,1]` does not reach that configuration within 1,000,000 steps. This is strong evidence that the current m2 word is correct in the Lean S1 encoder.

Thus: do not change `markerWord 2` based on my earlier warning. The previous claimed h-1/h-2 mismatch was an artifact of my incomplete target word. I apologize for the false alarm. I am now turning the 27,959-step blank-root simulation into a finite-run witness for the actual initial S1 configuration.
