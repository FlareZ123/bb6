# External A-step chain: packet normalization after the DRegular exit

This note extends `Astep2BoundaryReplay.md`. All call numbers refer to the 107 external `A_step2` invocations.

## Packet grammar

For a suffix tail (Y), write

[
P(q,p;Y)=(01)^q,0,1^p,Y.
]

The first DRegular exit occurs after call 10 at regular suffix ((01)^4 1). Call 11 (E branch, (n=35)) outputs

[
P(0,8;F_7),qquad F_7=0,1^6,
]

i.e. suffix `0111111110111111`.

## Exact packet trace (canonical form)

Use \(P(q,p;Y)=(01)^q0\,1^pY\), with canonical tail \(Y\) empty or beginning with 0. Absorb any leading ones of a proposed tail into \(p\). The suffixes after calls 11–30 parse as:

| Call | Branch | \((q,p)\) | Tail |
|---:|:---:|:---:|---|
| 11 | E | (0,8) | \(F_7=0111111\) |
| 12 | E | (2,5) | \(F_7\) |
| 13 | B | (1,5) | \(F_7\) |
| 14 | B | (0,5) | \(F_7\) |
| 15 | E | (2,2) | \(F_7\) |
| 16 | B | (1,2) | \(F_7\) |
| 17 | B | (0,2) | \(F_7\) |
| 18 | E | (0,6) | \(Y_3=01010111\) |
| 19 | E | (2,3) | \(Y_3\) |
| 20 | B | (1,3) | \(Y_3\) |
| 21 | B | (0,3) | \(Y_3\) |
| 22 | E | (2,0) | \(Y_3\) |
| 23 | B | (1,0) | \(Y_3\) |
| 24 | E | (0,9) | \(U_6=010111\) |
| 25 | E | (2,6) | \(U_6\) |
| 26 | B | (1,6) | \(U_6\) |
| 27 | B | (0,6) | \(U_6\) |
| 28 | E | (2,3) | \(U_6\) |
| 29 | B | (1,3) | \(U_6\) |
| 30 | B | (0,3) | \(U_6\) |

The B steps decrement \(q\) by one and preserve \(p,Y\). The E steps with \(p\ge3\) add two to \(q\), subtract three from \(p\), and preserve \(Y\). These are exactly the PacketRank.advance updates. Call 17 is the P2 leaf; call 18 is the e_two_reset output, and calls 19–23 continue with \(Y_3\).

Call 24 is an E-zero boundary. In canonical form it maps \(P(1,0;Y_3)\) to \(P(0,9;U_6)\), where \(U_6=Y_3\) with its leading \(01\) removed. Calls 25–30 again follow the ordinary B/E packet-rank updates with \(U_6\) preserved.

## The uncovered P2 residue

Let (N_{17}) be the unary parameter after call 17 and set

[
k=(N_{17}-4)/3.
]

The replay gives (k\equiv169\pmod{243}), so (k=243t+169). The P2 reset quotient is

[
h=(2k+1)/3=162t+113.
]

Thus call 18 is (N_{18}=1+12h=8k+5), and the E packet step at call 19 is (N_{19}=1+32h=5184t+3617), with (N_{19}\equiv26\pmod{27}).

This is not one of the existing `EChainBEEAReentry` residue corridors (k\equiv88,97,124,193,202,220,229\pmod{243}), nor the `EChainDoubleBReentry` (27t+17) or `EChainBEExit` (27t+20) corridors. It gives a concrete missing P2 residue class to investigate.

## Research consequence

The external halting-cylinder proof is not an opaque 107-step list after its first regular-language exit. It factors into:
1. the ten-step regular DRegular prefix ending at E,((q,b)=(4,1));
2. a packet (P(0,8;F_7));
3. PacketRank B/E normalization and an exact P2 reset;
4. a second packet tail (T_7), followed by further packet cycles.

The next useful proof target is the call-24 E-zero marker transformation (P(1,0;Y_3)\to P(0,8;T_7)), then the analogous marker transformations later in the trace. A general packet-tail transducer would be more valuable than adding isolated residue cases. This remains intermediate computational evidence; it is not a blank-tape reachability proof or a BB(6) result.
