# Raw42 B1=1RE: exact Lean-accepted short side cycles (2026-11-28)

**Research state:** 20 theorem instances kernel-checked against original machine semantics in two independently successful source-closure CI runs, no `sorryAx` or `native_decide`. These are local nonhalting cylinders inside the **still-unaccepted** whole Raw42/1RE child, not an unconditional Raw42 parent result.

Parent partial table is `1RB---_1RC---_0RD---_1LD0LB_------_------`. First unknown B1 is fixed to `1RE`, leaving six transition slots. A Raw42 raw completion counts 25 options (24 nonhalting transitions plus halt) for each undefined slot.

**First certificate source:** [Raw42OneRESecondCycles.lean](Raw42OneRESecondCycles.lean) exports four independent `Cover (WeightedBound B)` theorems fixing `B1=1RE` and `E0∈{0LB,0LD,0RD,1RD}`. [CI 46157202695](https://github.com/FlareZ123/bb6/actions/runs/46157202695) source-accepted all four `.cover` declarations, each depending on standard `propext, Classical.choice, Quot.sound` only. These cylinders cover exactly `4×25^5=39,062,500` raw completions.

**Second certificate source:** [Raw42OneREZeroRBThirdCycles.lean](Raw42OneREZeroRBThirdCycles.lean) holds `B1=1RE, E0=0RB` and fixes `E1` to one of:
`0LB,0LD,0LE,0RA,0RB,0RC,0RD,0RE,1LB,1LD,1LE,1RA,1RB,1RC,1RD,1RE`.
[CI 46158042663](https://github.com/FlareZ123/bb6/actions/runs/46158042663) succeeded, output `PASS: 16 distinct .cover theorems, only standard Lean axioms`. These are 16 distinct third-level partial machines and cover `16×25^4=6,250,000` raw completions.

The two lists are pairwise disjoint by first branching on `E0`; all 20 are also disjoint from any B1 branch other than `1RE`. Their union therefore proves nonhalting for **45,312,500 distinct normalized raw completions**. The proof consists of bounded, kernel-reduced `zipCycle` booleans together with the mathematically proved `zipCycle_sound` that universally lifts each finite side-cycle to all completions of the partial table.

**What it does NOT prove:** A whole `B1=1RE` Cover, reduction from the global conditional 38 residual roster, a new universal BB(6) upper bound, or the exact value of BB(6).

**In-progress extension:** `Raw42ZeroLESecondCycles.lean`, `Raw42OneLESecondCycles.lean`, and `Raw42OneLBSecondCycles.lean` propose 9 additional second-level certificates each; `Raw42ZeroLEZeroLBThirdCycles.lean` proposes 15 third-level; four large `Raw42*ThirdBatch.lean` files propose 557 third-level source-only candidates discovered through deterministic finite runs. Initial CI errors on negative Int literal parsing were corrected by parenthesizing boundaries in commits `523e923` and `4deae42`. These are **not** counted here until successful source acceptance. The 1LB whole child is already accepted, so its third-level candidates are redundant for frontier closure.

**Complement strategy:** The three still-unaccepted whole children `B1=0LE,1LE,1RE` each have exact original-source eight-shard DFA certificate archives under `im-results/agent32-raw42/`; workflows `agent32-raw42-e-split.yml` and `agent32-raw42-e-leaf-recover.yml` address expensive certificate kernel computation. Partial side cycles are mathematically valid additional subfamilies but do not replace complete original-source children.

Recorded 2026-11-28T15:21:24.138Z. 
