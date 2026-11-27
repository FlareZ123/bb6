# F197 reset-growth strategy

Status: intermediate proof architecture.  This does not yet close Raw132/F197.

Let a reset state mean the recurring B-boundary with terminal right word `e`.
For a reset left run word W, let `bits(W)` be its literal tape-bit length.

The exact rewrite families isolated so far all strictly increase this measure:

- paired-AA family
  `P^n Z(c_0,...,c_q) A A X -> P^n Phi(c_0,...,c_q) X`:
  **+2 bits exactly**;
- descent family
  `P^n M X -> P^(n-2) M K X`:
  **+2 bits exactly**;
- `J X -> T T X`: **+5**;
- `P J X -> A U J T X`: **+3**;
- `A U J X -> T T J T X`: **+5**.

The two +2 identities are purely algebraic.

For paired-AA, if `t` of the `q+1` data letters are T, then

```
bits(Z AA)  = 6q + 6 + 2t
bits(Phi)   = 6q + 8 + 2t.
```

A preserved leading `P^n` contributes `8n` on both sides.

For the descent, `bits(P)=8`, `bits(M)=21`, `bits(K)=18`, hence

```
8n + 21  ->  8(n-2) + 21 + 18 = 8n + 23.
```

The boundary increments follow from
`bits(J)=3`, `bits(TT)=8`,
`bits(PJ)=11`, `bits(AUJT)=14`,
`bits(AUJ)=10`, and `bits(TTJT)=15`.

## Sufficient closure theorem to target

A complete F197 nonhalting certificate can be reduced to the following
finite-state language problem.

1. Prove the blank orbit reaches a reset state in a finite exact number of
   literal steps.
2. Define a language `R` of well-formed reset left words containing that
   seed.
3. For every `W in R`, prove one exact positive-step reset rewrite
   `B(W,e) -> B(W',e)` with `W' in R`.
4. Prove every such rewrite satisfies `bits(W') >= bits(W)+1`
   (the presently known branches give at least +2).

Then iteration gives infinitely many distinct reset states at strictly
increasing tape length.  Since each reset-to-reset edge is a finite positive
literal execution with no intermediate halt, the original machine cannot
halt.

This formulation avoids trying to prove that all words over the observed
alphabet are safe; that statement is false.  The unresolved task is only the
closure of the *reachable transducer language*, principally the complementary
AT packet state.

## Empirical support, not proof

On the first 4,999 authentic reset transitions sampled from blank, the minimum
observed left-bit increment is +2.  Exhaustive one-step tests of all 32,766
pure A/T reset words of run length 1 through 14 also returned safely with
minimum +2, though 4,675 outputs introduced J/U/C markers.  Thus the growth
measure is robust experimentally, while pure-A/T closure is not.
