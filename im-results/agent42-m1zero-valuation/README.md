# M1, n = 8k: valuation-uniform source extension

**Status: intermediate computational result and Lean proof plan. Not a formal theorem.**

## Why this row matters

The current exported source theorem for marker 1 and n = 8k is
m1ZeroOdd_residue0_counted_increment_source in
im-results/agent48-counted-inc0/M1ZeroOddQ4Prefix.lean. It assumes k is odd.
The middle countdown revisits the class (m,n mod 8) = (1,0) every 24
one-step rows, while its quotient k decreases by 3 between visits. Starting
from an odd root quotient, the next visit has even quotient. The odd-only
hypothesis therefore does not close the repeated root itinerary.

The proposed extension removes that parity restriction by paying for the
2-adic valuation t = v2(k).

## Conjectured source theorem

For k > 0, write k = u * 2^t with u odd and t = v2(k). For admissible
L, a > 0, and arbitrary b, the original TM63 run is conjectured to satisfy

- q4 prefix length: 64 + 12*a + 12*t;
- q4 suffix length: 39 + 3*b;
- complete reset-prefix length: 103 + 12*a + 12*t + 3*b.

Since v2(8*k) = t+3, this total is exactly

resetPrefixCost 1 (8*k) a b
  = 48 + 12*(a + v2(8*k)) + 15 + 4 + 3*b.

The intended reset-prefix endpoint is

S1(L, 8*k-1, 0, a+b+2, 2^b-1, 0, h+5+3*b),

and the existing counted drain should then give the standard
m1ZeroOdd_residue0_counted_increment_source target with z=0 and right counter
2^b-1. At t=0 this specializes to the existing odd-k theorem.

## Discovered dynamic bridge

The 62-step finite bridge for k=1 has a fixed 44-step prefix. That prefix
does not read the boundary cell at relative position -14. For general t,
the input finite configuration is the existing M1ZeroOdd bridge start plus
3*t consecutive one-cells at

-14, -15, ..., -13-3*t.

The dynamic bridge decomposes as follows:

| Phase | Steps | Effect |
|---|---:|---|
| Fixed prefix | 44 | State 3 at head -14; boundary bit preserved |
| Left zero-bubble | 9*t | Consume t extra d1 blocks, moving the head left 3*t |
| Zero exit | 2 | State 3 on 0, then state 2 on 0; enter state 4 |
| State-4 setup | 4 | Enter state 3 at head -10-3*t |
| Right d1 scan | 9+3*t | Scan 3+t blocks of 111 |
| Final 110 boundary | 3 | Enter state 4 at relative head +2 |

Total bridge cost: 62 + 12*t.

The exact finite endpoint, with FConfig's list insertion order, has marked list

[1, -1, -4, -7, -10, -13,
 -16, -19, ..., -13-3*t,
 -14-3*t, -15-3*t, 2]

where the intermediate spaced marks are -16-3*i for 0 <= i < t.
The dynamic head window is [-15-3*t, 2].

The state-3 right scan is a cyclic variant of Agent48's state-1 scan
macros in M0EvenEightValuationMacros.lean. It converts each increasing-order
111 block to 100, i.e. the physical orientation of d0. The final boundary
starts on 110 and writes the 101 endpoint pattern.

## Binary-counter identity

Factor k = (2*u+1)*2^t. The source encoder identities give

binDec(L, 8*k)
  = d1pow(t+3) ++ d0 ++ binDec(L-t-4, u),

binDec(L, 8*k-1)
  = d0pow(t+3) ++ d1 ++ binDec(L-t-4, u).

Thus the bridge must convert the leading d1pow(t+3) ++ d0 to
d0pow(t+3) ++ d1, leaving the odd quotient tail untouched. This is the
same carry boundary already used in S1Encoder's binDec_carryPrefix and
binDec_sub_one_carryPrefix.

The fixed 44-step prefix reads only the first three d1 blocks, independent
of t. The next t blocks are the variable bubble. The q4 suffix can retain
binDec(L,8*k-1) as an opaque tail, as the existing odd-k target-left
identity already does.

## Reproducible experiment

Run:

    node im-results/agent42-m1zero-valuation/m1_zero_valuation_probe.js

The probe uses the exact TM63 table and S1 encoding, BigInt arithmetic for
the counter, exact finite-support tape equality, and FConfig's list update
order. It checks:

- the dynamic finite bridge for every t = 0,...,100, including its exact
  endpoint list and head window;
- the complete q4 prefix plus q4 suffix for t = 0,...,100,
  odd u in {1,3,5,7,9,11,13,15}, a in {1,2,3}, and b in {0,1,2};
- 7,272 source configurations, with no mismatches;
- the resetPrefixCost identity for every tested valuation.

This is bounded computational evidence, not a proof of the all-k theorem.

## Lean proof route

1. Add a fixed-prefix lemma analogous to M0EvenEightValuationFixedPrefix:
   parameterize the bit at -14, prove the 44-step finite trace, and confine
   all prefix heads to the fixed window.
2. Use binDec_carryPrefix to show the first three d1 blocks match the fixed
   prefix input for every t; leave the t remaining d1 blocks outside its
   frame.
3. Apply counted_left_sweep to the 3*t one-cells. The zero boundary at the
   new head and the 9 fixed one-cells to its right establish the two-step
   zero exit and the 3+t block scan.
4. Prove a state-3 rightward block macro (111 -> 100) and its n-block
   iteration, plus the three-step 110 boundary.
5. Lift the dynamic bridge with bridgeAt over [-15-3*t,2].
6. Reuse the E-scan, q4 right interface, parity-free q4 suffix target-left
   identity, and existing generic counted drain.
7. Prove v2(8*k)=v2(k)+3 and the resetPrefixCost equality. Then expose the
   all-k counted-increment theorem.

## Root integration boundary

This is a local S1 counted-increment source theorem, not a blank-root
reachability theorem or BB(6) certificate. It closes the even-k instances
of the (m=1,n mod 8 = 0) row only after the Lean proof is completed and
integrated into the 24-state middle countdown. The root's initial quotient
is odd, but the repeated row has quotient k-3, which is even; this is why
the odd-only theorem is insufficient for the whole countdown.
