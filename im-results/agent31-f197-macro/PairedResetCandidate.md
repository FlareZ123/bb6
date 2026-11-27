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

## Exact transducer decomposition now encoded in Lean

The n=0 family has now been decomposed into two recursive exact machines:

- `PairedScanCore.lean` / `PairedTerminalCore.lean`: packet rules
  `AT` (8 steps), `TT` (18 steps), and terminal `AAA` / `TAA`
  (47 / 57 steps).
- `PairedScan.lean`: recursive scanner from
  `c0 (T c1)...(T cq) AA X` to a J-headed decoder word.
- `PairedDecoderCore.lean`: eight 60/64-step local decoder peels plus the
  T-base.
- `PairedReset.lean`: composition of scanner and decoder for every nonempty
  Boolean data list.  This theorem is still **pending a green CI run**; keep it
  in `im-results/` until the no-`sorryAx` kernel check succeeds.

The decomposition gives the cost formula without fitting:
scanner cost `47 + 8q + 10t`, decoder cost `27 + 60q + 4t`, hence
`74 + 68q + 14t` for n=0.

It also gives an exact growth identity.  If there are q+1 data bits and t of
them are T, the source core has `6q+6+2t` tape bits while the output core has
`6q+8+2t`.  Therefore every paired-AA rewrite increases left reset
bit-length by **exactly 2**.  The already-derived P^n M descent also has
exactly +2 bit growth; the three J-boundary rules have +3 or +5.


## Complementary AT branch: carry-state reduction

The apparent `AT` parser obstruction is smaller than it first looks.  After
a maximal leading `P^n` is stripped, the paired parser reads an initial data
letter and then packets `T c_i`.  If the first non-continuation packet is
`AT` rather than `AA`, the already-understood scanner can still consume
all preceding data packets.  Only the final data letter and `AT` remain.

Thus there are exactly two terminal source forms:

```
A A T Y = P Y
T A T Y.
```

The first is literally a carried P into the suffix; the second is one new
finite terminal case.  Therefore the complementary branch should be modeled
as a small **carry state** (P-carried suffix versus TAT terminal), not as a
catalogue of all J/U/C marker outputs seen after a complete reset.

This observation suggests the next proof architecture: reuse the parametric
scanner for the prefix, add exact terminal lemmas for P-carried and TAT
states, and recurse on the suffix transducer.  It also explains why attempts
to assign one context-free replacement to the whole AT branch fail.


## Why the leading-P lift costs 68 per block

The empirical `+68n` term for a preserved leading `P^n` is not an opaque
fit.  It matches the two exact transport mechanisms already present in the
machine:

- each leading P is consumed into the right-side stack at **36** primitive
  steps per block;
- the same stored unit is restored through the J-headed decoder at **32**
  primitive steps per block.

Thus each carried leading P contributes `36+32=68` steps while reappearing
unchanged on the left.  This suggests a clean proof of the full n-family:
generalize the n=0 scanner to an initial right stack containing the P-counter,
then use the existing parametric decoder to restore that counter after the
paired data have been decoded.  No new fitted constant is needed.
