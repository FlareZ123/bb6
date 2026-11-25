# Raw42: initial certified child cut

Parent `1RB---_1RC---_0RD---_1LD0LB_------_------` (canonical surviving raw index 42, path address 1RC,0RD,1LD,0LB), first query B1 at time 6. Seven unknown slots, 25^7 = 6,103,515,625 raw completions.

**New symbolic proof:** for B1=1RD, start after 9 steps in state B on the left blank, right word 0 followed by 3 ones. If the right word contains k=2n+3 ones, the three-step right transfer consumes one one and moves the gap right; a five-step boundary turn adds two ones; a three-step left transfer per old one returns to the left blank. The next word contains k+2 ones, after 6k+5 steps. All arbitrary-tail transfers and the unbounded induction are checked by Lean in Raw42RDGrowth.lean using the accepted SweepPumping module. The six unknown slots are never consulted. Thus all 25^6 = 244,140,625 completions of this child never halt.

Raw42Cut.lean checks the first-hole split, the halt child at weighted bound 12, and seven additional direct side-cycle certificates for B1=0LB,0LC,0LD,0RC,0RD,1LD,1RC. The parent partition therefore discharges 9 of the 25 B1 choices (eight ordinary moves and halt), covering 2,197,265,625 raw completions, leaving sixteen ordinary children (3,906,250,000 completions). The theorem `BB6.Agent32Raw42.cover_parent` composes all remaining child Covers at any B >= 12. This is a partial cut, not full Raw42 closure or a decrease in the count of surviving canonical parents.

Both files checked locally with Lean 4.36.0-rc2 against the real source dependencies from accepted Raw59 artifact 15054146521; growth uses propext and Quot.sound only, partition and composition use propext, Classical.choice, Quot.sound. No native_decide or sorry. Fresh source CI not yet run. Parent source identity is the exact path-derived definition; `rd_eq` checks table equality by kernel computation.

Next: classify the sixteen retained children; exploit E/F renaming where permitted, reuse existing finite automata and symbolic sweep certificates, and preserve every unresolved leaf.
