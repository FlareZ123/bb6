# Blank-root reset pump: a 3,128,157-cycle finite phase

**Status:** reproducible computational finite-orbit result plus an elementary algebraic macro identity. Not a proof that the root run is infinite, not a nonhalting proof, and not a BB(6) result.

## Exact macro identity

Let the high branch be
\[
F(u,w)=(2u+3,\;w-2u-3).
\]
After \(m\) consecutive F steps from \((0,W)\),
\[
u_m=3\cdot2^m-3,\qquad
w_m=W-6\cdot2^m+6+3m.
\]
For \(m=26\),
\[
(u_{26},w_{26})=(201326589,\;W-402653100).
\]
If
\[
402653100\le W\le805306272,\qquad W\equiv0\pmod4,
\]
then \(w_{26}\) is divisible by four and
\[
0\le w_{26}\le402653172=2u_{26}-6.
\]
Consequently the ordinary transition is the even-\(w\), odd-gap reset Eodd, which sends
\[
(u_{26},w_{26})\longmapsto(0,\;2u_{26}+w_{26}+10)=(0,W+88).
\]
Thus, throughout this interval,
\[
(0,W)\xrightarrow{F^{26}E_{\rm odd}}(0,W+88)
\]
in exactly 27 transitions. The interval and congruence conditions are preserved by the +88 return map until the upper endpoint is crossed.

## Actual blank-root segment

The C++ reproducer below transcribes the transition cases from Agent 5's BB429Rank.next and checks the entire finite segment from the blank root:
- The first occurrence of \((0,530028452)\) is reached after exactly 149,997,313 transitions.
- From there, 3,128,157 consecutive 27-step blocks each have the exact tag word \(F^{26}E_{\rm odd}\).
- Each block returns \((0,W)\) to \((0,W+88)\), with all intermediate W values satisfying the macro's interval and divisibility hypotheses.
- The segment ends at \((0,805306268)\), after exactly 234,457,552 total transitions from \((0,0)\).

The arithmetic checks are:
\[
805306268-530028452=88\cdot3128157,
\]
\[
234457552-149997313=27\cdot3128157.
\]
The next W value under this return map would be 805306356, outside the interval, so this particular macro phase terminates at the displayed endpoint. No claim is made here about the subsequent trajectory.

## Reproduction

Compile and run:

    g++ -O3 -std=c++17 BB429RootResetPump.cpp -o /tmp/bb429-reset-pump
    /tmp/bb429-reset-pump

Expected output:

    prefix: (0,0) -> (0,530028452) in 149997313 steps
    verified cycles: 3128157 x (F^26 Eodd), each 27 steps, W += 88
    final: (0,805306268) at step 234457552

## Research significance and limitation

This is a long exact finite prefix, not an infinite-run argument. It exposes a first-return pump on the section \(u=0\): a fixed inverse/forward macro increments the second counter by 88 for over three million cycles, then reaches a phase boundary. Similar but different reset-pump words appear in later simulation windows. A promising next task is to classify the piecewise-affine first-return map across phase boundaries and prove that the actual root's sequence of reset states remains in a domain on which the return map is always defined. Only such a global invariant could turn these finite pumps into a nonhalting proof.

The long reset-containing plateaus are also concrete finite examples of why an infinite root itinerary can look periodic for millions of cycles while still needing a phase-change/aperiodicity argument.
