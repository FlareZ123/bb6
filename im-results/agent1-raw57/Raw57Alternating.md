# Raw57/1LA alternating-counter pair

Two one-hole partial machines have exact blank-root four-phase growth proofs in the literal executable zipper semantics. Original-source import and `NeverHalts` adapter await acceptance. This is an intermediate leaf result, not a Raw57 parent Cover.

| Open index | Literal table | Epoch cost from parameter n |
|---|---|---|
| 748 | `1RB1LA_1RC0LF_0RD0LE_1LD1RE_0RF0LA_---1RC` | 360+160n |
| 944 | `1RB1LA_1RC0RD_0RD0LE_1LD1RE_0RF0LA_---1RC` | 292+128n |

In the original Z0 convention, left includes the scanned cell and both lists are nearest-first, blank-padded. Let S(n,R) be state A with empty left list and right word 11(01)^(2n+1)R. Blank reaches S(0,empty) after 9 primitive steps. For both tables a reset and three increments yield the exact epoch:

    S(n,empty) -> S(n,10101) -> S(n+1,101) -> S(n+2,1) -> S(n+3,empty).

The initial scan uses an F-state four-bit alternating block transfer. For nonempty suffix, the fixed 13-step turn creates an A-state left alternating word and right frame 11101. The backward sweep consumes each left pair 01 and adds it just after right frame 111, at 18 or 14 steps. A fixed final return restores the section frame 11 and adds the final pair. The empty-suffix branch has two additional fixed carry macros; together they consume one left pair and synthesize the three-token suffix. All the local transitions hold for arbitrary untouched list tails by definitional reduction. Induction using the existing sweep lemmas establishes the unbounded epoch, not an extrapolation from simulation.

Source: [Raw57Alternating.lean](Raw57Alternating.lean), namespace `BB6Coverage.Agent40Raw57Alternating`. Parameter false is 748 and true is 944. Local Lean 4.36.0-rc2 accepted all nine macros, `epoch`, `epochCost_formula`, `entry`, `growth`, `live_prefix` against the literal copied original `move0`, `step0`, `run0`, and sweep lemmas; axiom sets at most [propext, Quot.sound]. The checked local file differs from the committed source by import of the copied core and omission of the original `never_of_growth` adapter. The committed `never` theorem still needs source-connected verification; no accepted parent count is claimed. The intended consumer must verify both exact literal table equalities before consuming the new proofs. See [the maintained Raw57 dossier](README.md) for the remaining parent obligations.
