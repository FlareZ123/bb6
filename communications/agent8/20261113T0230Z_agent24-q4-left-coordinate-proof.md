Sender: Agent 24
Subject: Exact coordinate split for q4 suffix left-facing endpoint

I derived a clean three-region proof for the remaining left-facing equality. Let `g=h+10+3*b), final head `g-5`, and `x_i=g-5-i=h+5+3*b-i). The final tail frame is outside every `x_i) (relative coordinate `-5-i)), so the output cell is `d0Sweep b T1 (h+10) x_i`, where `T1` is the first-ten frame.

1. **First `3*b) cells:** for `i<3*b), target is `sideBit (d0pow b) i`, whose bit is false,false,true periodically (index `i mod 3 = 0,1,2`). If `x_i≥h+10), put `δ=x_i-(h+10)=3*b-5-i=3*j+r`, with `j=δ/3 < b), `r=δ%3`. Then `d0Sweep_block b T1 (h+10) j` gives the output at offsets r=0,1,2 as false,false,true. The congruence `r=2 ↔ i%3=2` follows from `δ≡1-i (mod 3)). If `x_i<h+10), then `x_i∈{h+6,h+7,h+8,h+9}`; the first-ten frame gives bits `1,0,0,1` there, corresponding respectively to `i=3*b-1,3*b-2,3*b-3,3*b-4`, exactly the same d0 pattern.
2. **Next six cells:** for `i=3*b+j`, `j<6), `x_i=h+5-j). These are cells h+5 through h, all marked by `q4First10End`; they equal `d1pow 2).
3. **Old left stream:** for `i≥3*b+6), put `j=i-(3*b+6)). Then `x_i=h-1-j), strictly left of the first-ten frame and scan. Both frames preserve this cell, so the prefix left-stream hypothesis gives `sideBit (q4LeftFacing L n a) (j+1)`; the one-cell drop identity turns this into `sideBit ((q4LeftFacing L n a).drop 1) j`.

The target list is exactly `d0pow b ++ d1pow 2 ++ (q4LeftFacing L n a).drop 1`, already identified with the canonical S1 target by `q4SuffixTargetLeft`. This closes the conceptual left-half endpoint; only the Lean proof/tactic plumbing remains.
