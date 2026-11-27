# Raw13 mirrored binary counter: exact exponential return

**Claim (locally kernel-checked against recovered repository dependency objects; full source CI pending).** The literal partial table
`1RB1LD1RC1RE1LA1RE1LC0LA0RF1RA---0RB`
has an infinite blank-start orbit. Its only unassigned entry is F0. The derivation below uses only assigned transitions, and therefore applies to every compatible completion. This is one previously unresolved Raw13 coupled-six-hole leaf (E1=1RA), not a complete sibling or a global roster reduction.

## Configuration and return

Use the head-inclusive left word and head-exclusive right word of the original zipper, in nearest-first order. Write A(l,r) for state A, and concatenate words by juxtaposition. Let
H=1111, D0=0011, D1=1011, X=001, Y=011, U=111, Q=0101, R=1010, S=01011, T=11011, pre=01010.
For k≥0 define body(k,W)=Q^(k+1) 0 U^(k+1) 1 W and root(k)=A(empty,body(k,S)). Equivalently root(k) has right word (01)^(2k+3) 1^(3k+3) S. Direct exact blank replay reaches root(0) at step 48.

For a little-endian bit list b let d4 encode 0→D0, 1→D1 and d3 encode 0→U, 1→Y. Define
`frame(b)=A(H D0 d4(b) 1, 1 d3(b) S)`.
The two words encode the same counter. The fixed low D0 is a work digit, not part of b.

**Exact return:** root(k) → root(k+1) in 52·2^k+4 primitive transitions, without accessing F0. Consequently root(k) occurs at 48+52(2^k−1)+4k=52·2^k+4k−4. This makes arbitrarily long live prefixes and proves nonhalting of all compatible completions, by the kernel-checked identities below.

## Primitive word rules

L and W are arbitrary untouched tails; the two explicitly blank-sided rules say so. Each row is a finite literal transition calculation, with no access to unspecified tails. The letters before parentheses denote states.

| Source | Steps | Destination |
|---|---:|---|
| A(0L,pre W) | 5 | B(000111L,W) |
| B(0L,R W) | 4 | B(0 D0 L,W) |
| B(0L,U W) | 3 | A(H L,W) |
| A(H D0 L,1W) | 9 | B(1 X T L,W) |
| B(1L,Y W) | 3 | B(1 X L,W) |
| B(1L,U W) | 2 | A(U L,1W) |
| A(U L,W) | 3 | D(L,101W) |
| D(X L,W) | 3 | D(L,U W) |
| D(T L,W) | 5 | A(H L,0W) |
| A(H D1 L,W) | 8 | A(H L,Q W) |
| A(H L,W) | 4 | A(L,Q W) |
| B(1L,S), blank beyond S | 9 | A(11111 X L,1) |
| A(11111L,W) | 5 | D(L,10101W) |
| A(H1,W), blank beyond left word | 14 | A(empty,Q Q W) |

All fourteen finite rules were independently replayed with an open-tail simulator that stops on a read past a supplied finite prefix, except for the stated blank side. In particular the terminal turn contributes one extra X block; omitting it changes the exact return cost. The Lean module `Raw13Coupled6MirroredCounter.lean` expresses every row as a definitional equality with arbitrary tails and uses the existing `SweepPumping` induction theorems.

## All-width proof

The setup identity, obtained from the first three rules (5 + 4j + 3 steps), is
`A(0L,body(j,W)) → A(H D0^(j+1) 1L, 1 U^j W)`.
Here body(j,W)=pre R^j U 1 U^j W by elementary rotation of the repeated words. Blank left and a single explicit zero have identical first transitions. Thus root(k) reaches frame(0^k) in 4k+8.

For carry length j, apply the fourth rule, the fifth j times, then the sixth, seventh, eighth j+1 times, and ninth. This produces the **carry core**, of cost 6j+22:
`A(H D0 L,1 Y^j U W) → A(H L,0 U^(j+1) 1 Y W)`.
Take L=D1^j D0 L'. Apply the tenth rule j times and the eleventh once; the result is A(D0 L',body(j,Y W)). Apply setup with L=011L'. The final result is
`A(H D0^(j+1) D1 L',1 U^j Y W)`
at total cost 18j+34. Hence frame(1^j 0 b) goes to frame(0^j 1 b) with that exact cost. This is ordinary binary increment, regardless of the high bits b. The arbitrary-tail rules guarantee that high digits are protected, not just matched on finitely many examples.

For full overflow from frame(1^k), perform the same entry and k forward Y sweeps, then the explicit blank terminal turn, dropFive, k+2 left X sweeps, and leftExit. The cost is 6k+34 and the result is A(H D1^k 1,0 U^(k+2) 1 S). Pop k one digits at cost 8k and apply the final 14-step blank-left rule. This is root(k+1), with total overflow cost 14k+48.

The exact cost F(k) of filling k binary digits from all-zero to all-one is F(0)=0 and F(k+1)=2F(k)+18k+34 (two k-bit fills around the carry into the high digit). Induction gives F(k)=52·2^k−18k−52. Setup + fill + overflow therefore costs (4k+8)+F(k)+(14k+48)=52·2^k+4, strictly positive for all k. The seed and this family establish an infinite assigned-transition trajectory.

## Evidence boundary and next step

Independent JavaScript replay checked every increment for widths 0–7 (247 cases), every setup/overflow at those widths, and the exact return times. The arbitrary-tail finite calculations and the induction, rather than that finite sample, are the mathematical argument. The first source-pinned run [46037473169](https://github.com/FlareZ123/bb6/actions/runs/46037473169) rejected list-association elaboration in three sweep joins and the final overflow. The corrected module compiles locally with Lean 4.36.0-rc2 against the accepted repository proof objects recovered from artifact 15099506359. Both `rootGrowth` and `never` report exactly `[propext, Quot.sound]`. The sibling generator now selects the exact literal theorem for E1=1RA. Full source-closure CI is still pending; do not infer a complete sibling or global roster reduction. No BB(6) solution is claimed.
