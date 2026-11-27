# F197 paired-prefix reset candidate

Status: **exactly reproduced computational identity, not yet a mathematical proof or Lean theorem.**
This is a new candidate family extending the two q=0 families in
`im-results/agent2-f197-sweep/ParametricReset.md`.

Use the reset alphabet from that note:
`A=(1,1)`, `T=(2,2)`, `P=AAT`, terminal `e=(1,0)`.
For a letter `c in {A,T}`, define

```
H(A) = A T
H(T) = A A T = P.
```

Choose `q >= 0`, letters `c_0,...,c_q in {A,T}`, and set

```
Z(c_0,...,c_q) = c_0 (T c_1) ... (T c_q)
Phi(c_0,...,c_q) = A H(c_0) ... H(c_q).
```

The candidate exact reset identity is, for every `n >= 0` and well-formed
nonempty suffix `X`,

```
B(P^n Z(c_0,...,c_q) A A X, e)
  -->
B(P^n Phi(c_0,...,c_q) X, e).
```

If `t` is the number of T letters among `c_0,...,c_q`, the candidate exact
primitive cost is

```
68 n + 68 q + 74 + 14 t.
```

For `q=0,c_0=A` this is exactly the already-derived
`P^n AAA X -> P^(n+1)X` family (cost `68n+74`).
For `q=0,c_0=T` it is exactly
`P^n TAA X -> P^n AAAT X` (cost `68n+88`).

Examples at n=0:

```
ATAAA  -> AATAT        cost 142
TTAAA  -> AAATAT       cost 156
ATTAA  -> AATAAT       cost 156
TTTAA  -> AAATAAT      cost 170
ATATAAA -> AATATAT     cost 210
```

## Evidence

The identity, full output word, and exact primitive cost were tested against
the independent BigInt implementation of the already-derived exact grouped
F197 return map on:

- 5,200 random instances with `n=0`, `0<=q<=25`, arbitrary A/T data, and
  arbitrary suffixes over `A,J,T,C,U` ending in `e`;
- 8,000 further random instances with `0<=n<=20`, `0<=q<=20`, arbitrary
  A/T data, and arbitrary suffixes over `A,J,T,C,U` ending in `e`.

There were zero endpoint or exact-cost mismatches.

On the first 8,000 authentic reset transitions from blank, this one candidate
family alone explains 4,930 exact transitions.  Together with the new
`P^n M` descent and the three J-boundary rules in `RESET-DESCENT.md`, the
current symbolic rules explain 6,328 / 8,000 = 79.1% exactly.

## Structural clue

The source parser reads `c_0` and then two-run packets.  Packets `T A` and
`T T` continue the data word; the terminating packet `A A` triggers this
family.  The only fourth packet `A T` is precisely where the reset output can
introduce the rare `J/U/C` markers.  This gives a natural next decomposition:
prove the `AA` branch above, then derive a finite/recursive transducer for
the complementary `AT` branch.

An exhaustive experiment over every A/T word of run length 1 through 14
(32,766 words) found no halt or timeout on the next reset and every left
bit-length increased by at least 2, but 4,675 outputs left the pure A/T
alphabet through J/U/C markers.  Therefore “A/T is closed” is false; the
paired packet decomposition is the stronger surviving structure.

Do not cite this file as a proof until the grouped-map induction or Lean
formalization is completed.
