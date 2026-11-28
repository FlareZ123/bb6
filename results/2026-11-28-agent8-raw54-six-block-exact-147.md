# Exact weighted halting threshold 147 for a Raw54 two-hole cylinder

The cylinder `1RB---_1RC1RF_0RD---_1LD0LE_1RA1RD_0RE0LF` (free A1 and C1) has exact weighted halting threshold 147. This is a local original-source Lean 4.36.0-rc2 theorem, not an assertion of acceptance by a new CI run. The 625 normalized completions are covered. The bound includes blank-delay weighting and the halt query; the attaining completion A1=1LA, C1=halt has 146 live moves.

## Unbounded return mechanism

All zipper words are written nearest the head first, with the scanned cell in the left word. Let P=1111110, Q=0000011, L=001110, R=101110. In state D, the exact arbitrary-tail transitions are:

- L P u | v -> L u | Q v in 27 moves;
- L | v -> R | 1v in 21 moves;
- R u | 1Qv -> R P u | 1v in 9 moves;
- R u | 1 -> L P u | empty in 9 moves.

Consequently D(L P^k, empty) returns to D(L P^(k+1), empty) in 30+36k moves, for arbitrary A1 ordinary action. Eleven A1 actions have kernel-checked blank entries to this family. Three more frontier actions have exact modified returns: 1RE adds one block in 244+108k moves, 0RF carries a moving defect through a two-phase epoch of 338+144k moves, and 0RA adds four blocks in 1115+252n moves (equivalently 1115+1008k along its reachable n=4k orbit). The latter two explicitly retain the internal defects in their invariant; a single uniform-block hypothesis would be false for them.

The three further marked variants 0LF, 1LB, 1RB add one block in 98+36k, 100+36k, 94+36k moves, respectively. A1=1LF has an exact 4-cycle. Thus 18 ordinary A1 actions universally never query C1 and never halt. For the remaining six ordinary actions, first C1 query times are 100 (0LC), 104 (0LD), 100 (0RC), 146 (1LA), 100 (1LC), 100 (1RC). The parent first queries A1 at time 99. The existing last-hole and split certificate rules cover these branches exhaustively, including the halt actions and every compatible completion.

## Formal certificate

- [Common block return and eleven entries](../im-results/agent8-raw54/Raw54OneRDSixBlock.lean)
- [1RE and 0RF returns](../im-results/agent8-raw54/Raw54OneRDSixBlockExceptions.lean)
- [0RA four-block return](../im-results/agent8-raw54/Raw54OneRDSixBlockZeroRA.lean)
- [Complete parent audit, attainment, exact threshold](../im-results/agent8-raw54/Raw54OneRDSixBlockParent.lean)

The theorem `BB6.Agent8Raw54.SixBlock.exact_weighted_threshold` states
`(∀ m, compatible parent m → WeightedBound B m) ↔ 147 ≤ B`.
The `cover` theorem gives `Cover (WeightedBound 147) parent` directly. The local kernel reports only propext, Classical.choice and Quot.sound for these two theorems and propext, Quot.sound for attainment. No axiomatic simulation oracle or bounded-run extrapolation is used.

The source dependency slice is original-source artifact 15258411262 from the prior Raw54 audit. The fourteen targeted residual tables occur in the 187-element complement of the deterministic 440-certificate artifact 15268120290. Five additional certificates from the preceding agent run were reported separately without their literal roster, so overlap is not yet resolved: at least nine of these fourteen are newly covered relative to the reported 445. This result does not close the entire Raw54 E1=1RD frontier, the Raw54 root, or BB(6).
