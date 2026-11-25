# Raw107/1LA: complete source-accepted bound

The entire 1LA child has weighted bound **282** for every compatible completion. The `Raw107LABridge.lean` theorem is the exact graft of the eight nonhalting exceptions into the generated first-hole tree. All six disjoint certificate shards and final assembly passed [run 45527192650](https://github.com/FlareZ123/bb6/actions/runs/45527192650), pinned 1322639d1894ac7ba84ecd279b5c0a22ef1b547a. The first monolithic audit 45525325241 ended from runner shutdown, not a reported theorem error. The partitioned audit is the accepted replacement. This is a child closure, not a bound for all of raw107.

## Three unary-tail exceptions

Exact tables (source open-list indices): 
- 95: `1RB0LB_1RC1LA_0RD0RC_1LD1RE_0RF0RB_---0RC`
- 96: `1RB0LB_1RC1LA_0RD0RF_1LD1RE_0RF0RB_---0RC`
- 99: `1RB0LB_1RC1LA_0RD1LE_1LD1RE_0RF0RB_---0RC`

The unassigned transition is F0. In the exact zipper convention of SweepPumping (left includes the scanned cell), write P=01, K=11, J=001. All three enter B([], P^3 K) at t=37. Define R(k,b)=1 P^k K^b and U(k,b)=P^k K^b. The common strong-induction lemma is
```
B(J L, U(2n+2,b)) ->* A(L, R(2n+3,b+2^n))
```
for every n,b and arbitrary left suffix L. A fixed four-step transfer consumes 0101, then a repeated four-step sweep converts the remaining copies into 0001 blocks. The unary turn processes pairs of 1s in cost 2 (C1=0RC/0RF) or 6 (C1=1LE), converts the stored zeros back into pairs of 1s, and returns to A increasing b by 1. Each of n stored 0001 blocks initiates an already-proved smaller clear, whose unary increment is 2^j. Summing the geometric increments proves the stated arbitrary-tail lemma.

The outer return is
```
B([], U(2n+3,b+1)) ->* B([], U(2n+5,b+2^(n+1)-1)).
```
The number of alternating pairs strictly increases by two; the unary count stays positive because 2^(n+1)>=2. Thus all three partial tables have unbounded defined ordinary-step prefixes, never consulting F0. Every compatible completion is nonhalting. This is an inductive proof, independent of a simulation cutoff.

`Raw107LAUnary.lean`: all operational recurrence, entry and positivity lemmas passed local Lean 4.36.0-rc2 against exact copied zipper definitions and checked sweep lemmas (axioms propext, Quot.sound, Classical.choice for positive-cost witness). The committed source imports the original SweepPumping and uses never_of_growth; full source closure and axiom audit **passed** at [run 45525124908](https://github.com/FlareZ123/bb6/actions/runs/45525124908) on 0162dfb0190ca8434d71557317b3b21fdc80348d. Job 138906451980, step 43 `Check source-linked raw107 exceptional growth witnesses`, executed successfully and the forbidden-axiom output guard passed. All six exceptional proof modules, covering eleven leaf tables, were included. Exported interfaces: BB6.Agent1Raw107LAUnary.M95/M96/M99.table and .never.

Agent11/10 supplied the other five 1LA exceptions and three exceptions in other raw107 children. The complete raw107 parent requires the other child bounds and the parent first-hole split; the 1LA bound can now be used without premises.
