# Raw47 hard leaf 3423: complementary binary counters

Machine: `1RB1LF_1RC0RB_0RD0LE_1LD0RC_1LE0LA_1LA---` (the only unassigned slot is F1). It belongs to Raw47 depth-three parent 174. State A at a return point reads zero. All words below are nearest-first on their respective ray. Left encoding is `0b` for digit b, followed by implicit zeros; right encoding is `1b`.

## Invariant

At the chosen returns to A0, the left word encodes a finite canonical low-endian binary integer d (no redundant final zero), and the right ray is

```
(11)^(k+1) 00 enc(w) 01 T
```

where k>=0, w is a fixed-width low-endian binary word of length n, and T is an arbitrary finite tail. Let V denote low-endian binary value. Then

```
2^k (1+2 V(d)) + V(w) = 2^n.
```

Blank reaches k=0, d=[], w=[], T=[] in 15 moves.

### Decrement step (w nonzero)

Write w=0^j 1 s. The A/B/C/D/E prefix computation takes 2k+4j+14 moves and reaches A reading one, with left digits `0^k 1 d` and right word

```
00 (11)^j 10 enc(s) 01 T
```

This is an exact parametric identity, decomposed into fixed-frame sweeps in `Raw47Complement3423.lean`: A0 then 2k B1 moves and the final B1/B1/B0; j C0/D1 pairs; C0/D1/C1; j+1 E0 pairs; E1; four A0/B0/C1/E1 moves.

A1 and F0 form a two-move pair: pop a left digit `0b`, prepend `11` on the right and return to A reading b. The initial zero of every encoded digit (or the implicit blank ray) prevents F1. Repeat until the first zero digit. If the pushed digit list has r leading ones and residual d' after that zero, the elementary carry identity is

```
V(0^k 1 d)+1 = 2^r (1+2 V(d')).
```

The new k is r, and the right active word is w'=1^j 0 s, with V(w')=V(w)-1 and |w'|=|w|. Hence the balance is preserved. The new left digits remain canonical. The total return cost is 2k+4j+14+2(r+1)>0.

### Exhaustion step (w=0^n)

The balance becomes 2^k(1+2V(d))=2^n. Since the second factor is positive odd, k=n and V(d)=0. Canonicity forces d=[].

For any k,n with blank left ray, the exact reset identity takes 4k+4n+19 moves and returns to A0 with new parameters

```
k'=0, d'=[], w'=1^(k+1), T'=(11)^n 1 T.
```

To see the reset sweep: enter C0 after clearing the leading 11 blocks, do n C0/D1 pairs, C0 to D0, sweep n+1 pairs of zeros leftward in D0, then D1/C1, sweep k+1 pairs of zeros leftward in E0, and finish with E0/E1/A0/B0/C1/E1/A1/F0. With k=n the new balance is 1+(2^(n+1)-1)=2^(n+1).

Both transitions have positive cost, so inductively there are arbitrarily long defined runs. This proves nonhalting for every completion of the F1 slot once the exact sweep identities are established. No inference from a finite sample of run lengths is used.

## Status

Accepted at commit `e485f9a09285e3c353e5173fade517fe7ecfaa71`, CI run `45970441302`, job `140409318448`. `decrementPrefix`, `resetPrefix`, `goodStep`, `never`, and `BB6.Agent50.Raw47D3G174.all_quotient` checked with only standard axioms. All 23 open leaves of parent 174 were covered (22 FAR + this proof); accepted artifact `raw47-graph-parents` ID `15184886313`. The direct numerical macro test covered 3920 decrement-prefix and 1764 reset-prefix instances, including arbitrary finite tails, with zero disagreements; this is supplementary, not the proof.

The previous finite side-graph searches (including positional masks, aggregate run classes and two-alignment block summaries) had no witness for this leaf; the coupled arithmetic balance explains why purely independent side summaries can be inefficient.
