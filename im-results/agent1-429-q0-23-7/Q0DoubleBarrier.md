# Double-window rank barriers for the q0 signed path

The new theorem `q0_barrier` proves an entire interval exclusion from one Boolean certificate. This extends the one-row equivalence in [Q0RankBarrier.lean](Q0RankBarrier.lean). With B=a*16^k, it suffices to prove `barrier a k=true` to exclude every q0 parameter u satisfying

    24*u+22+6*k <= B
    B+5+12*k <= 48*u+37.

The root assumptions are exactly the existing Source interface and q0 equations n=23+32*u, x+24*u+19=13*2^n, y+13=2*x. The new theorem is conditional on the finite Boolean certificate; no uniform all-scale theorem is claimed.

## Why the interval works

Every signed path changes rank by 3..6 each step. Its first crossing of B has rank B+b, 0<=b<6. The two displayed margins guarantee at least k past steps and 2k further steps. Split the path at these positions and apply near_power to the past. Write the crossing ordinate as a*Dn(w)+e, with 3e<=a+b. The next k digits v are a carry trace reading w, and the next k digits z are a carry trace reading v. The first row starts at (b,e), ends at (q1,e1); the second row starts at exactly (q1,e1). Enumerate b+3k<=q1<=b+6k and 3e1<=q1+a, and all e in its initial bound. The checker searches these two rows columnwise using the same v digit in both, checks the seam and strict initial cone, and rejects any branch whose first-row final q1 cannot be reached in the remaining steps. Completeness is proved by induction on Carry. No ordinate of size 16^k is enumerated. This is DFS, not yet polynomial-time DP.

## Reproduction and status

Locally compiled Q0MacroCore.lean (blob 06821faeb7c97a2b6f65adb68cdc2f707dcfa03e), Q0RankBarrier.lean (blob 9272b3dfdff8895d0fe2d677cc35bf2b2be29ead) and Q0DoubleBarrier.lean (local blob 8af7ba62b2f41e954c255f80d287538993797e1c) on Lean 4.36.0-rc2; all printed theorems have only propext, Classical.choice, Quot.sound. No sorryAx. The following `#eval` calls returned true (scale 50 checked all six b individually):

    barrier 13 12
    barrier 13 20
    barrier 13 30
    barrier 13 40
    barrier 13 50

These are finite computations of the formally sound checker, NOT kernel reduction of the specific Boolean equalities. Direct `by decide` at scale 8 timed out. For k=12 alone the corresponding interval is 76232806192472 <= u <= 152465612384934; for k=50 its width exceeds 4.35e59 parameters. These intervals are sparse, not a continuous exclusion from zero. The all-scale barrier hypothesis remains open; sufficient coefficients with adjacent ratio strictly below 2 would yield contiguous coverage for large u, provided the margins are satisfied. The existing fixed-depth tests and the previous million-parameter exclusion should not be confused with this interval theorem.

Next: obtain a polynomial-width DP with a signed carry for the strict cone, then attack all-scale seam impossibility or certify a contiguous interval chain. Do not promote the intermediate result to a #429 decision.
