# F197 reset descent: exact parametric reduction

Machine: `1RB0RE_1RC0LE_0RD---_0RE0RA_1LF0LB_1LA1LF`.

This note isolates a recurring unbounded phase of the archived Raw132/F197
machine.  It is not yet a nonhalting certificate and not a `Cover`.

## Coordinates and run alphabet

At a reset boundary we are in phase B with terminal shortened right word
`e=(1,e)`.  In the literal `Macro.lean` coordinate the B right stack has
one additional guaranteed leading zero: `0 :: shortenedRight`.

Left run symbols:
- `A=(1,1)`, `J=(1,2)`, `T=(2,2)`;
- `P=AAT`;
- `M=J T P A A A`;
- `K=T A T P`.

Right run symbols used by the transport:
- `x=(1,1)`, `s=(5,3)`, `u=(4,3)`, `d=(2,e)`, `e=(1,e)`.

The reachable occurrences of the new family have the suffix after `M`
beginning with `T A`; this is the only suffix condition needed by the fixed
middle cores below.

## New descent identity

For every `n >= 2` and every continuation `X` in the reachable `T A`
frame,

```
B(P^n M X, e)  -->  B(P^(n-2) M K X, e)
```

with exact primitive transition count

```
68 n + 252.
```

The reduction factors into already-known/reset transport pieces and one fixed
middle computation.

For `n=2`:
1. consume two P blocks: 72 transitions, giving `B(MX, u s d)`;
2. fixed middle endpoint: 316 transitions, giving `B(M K X,e)`.

Total: `388 = 68*2+252`.

For `n>=3`:
1. consume `P^n`: `36n` transitions, giving
   `B(MX, u s^(n-1) d)`;
2. fixed middle core: 321 transitions, giving
   `B(J M K X, x s^(n-3) d)`;
3. decode the right counter: `32(n-3)+27` transitions, giving
   `B(P^(n-2) M K X,e)`.

Total: `36n + 321 + 32(n-3)+27 = 68n+252`.

The `n=3` case uses the terminal-`d` specialization of the 321-step core;
`n>=4` uses the arbitrary-tail specialization with one preserved `s`.

## Iterated form

Write `n=2q+r` with `r in {0,1}`.  Repeating the exact descent gives

```
B(P^(2q+r) M X,e) --> B(P^r M K^q X,e).
```

The summed primitive cost is

```
68 q (n-q) + 320 q.
```

Equivalently:
- even `n=2q`: `68q^2+320q`;
- odd `n=2q+1`: `68q^2+388q`.

## Exact parity endpoints

The remaining leading J phase has three small exact reset rewrites:

```
B(J X,e)     --> B(T T X,e)       in 21
B(P J X,e)   --> B(A U J T X,e)   in 75
B(A U J X,e) --> B(T T J T X,e)   in 39
```

Thus the entire J-cascade has a closed exact parity description:
- even descent ends at a `TT...` boundary;
- odd descent ends through `AUJ...` and then `TTJT...`.

## Lean artifacts

- `Macro.lean`: literal machine and sound four-phase macro semantics.
- `MacroExact.lean`: exact-cost macro iterator and soundness bridge.
- `ResetTransport.lean`: P-consumer and decoder transport cores.
- `ResetDescentCore.lean`: 94/95-step fixed macro cores.
- `ResetDescentFamily.lean`: parametric composition for n=2, n=3, and n>=4.
- `ResetBoundary.lean`: exact parity endpoint rewrites.

The focused manual workflow target is `f197-reset-core`.  At the time this
note was written the new exact-cost bridge was still being CI-checked; do not
treat the family as kernel-certified until that target reports success with no
`sorryAx`.

## Computational discovery evidence (not proof)

An exact BigInt implementation of the already-derived macro rules was followed
through the first 5,000 reset states:
- no halt was encountered;
- every reset left word used only `A,J,T,C,U,e` after the initial `d`;
- all 4,999 reset-to-reset left bit-length changes were positive (minimum +2);
- the new `P^n M` descent occurred hundreds of times, with observed exponents
  up to the hundreds and live cost exactly `68n+252`.

A longer 5,670-reset sample reached about 101.8 million live primitive
transitions with the same qualitative behavior.  These observations motivate
the rewrite but are not used as proof.

## Remaining obstruction

A coarse alphabet invariant is insufficient: randomly generated reset words
over the same run alphabet can halt, and safe random reset words need not gain
two bits.  The missing proof obligation is therefore a relational language for
the *reachable* reset words.

After the J-cascade the orbit enters a predominantly `T/A` prefix-rewrite
phase.  The two previously-known exact families

```
P^n AAA X -> P^(n+1) X
P^n TAA X -> P^n AAAT X
```

and the new J-descent explain much of the large trace, but rare `C/U/J`
boundary words still require a closed invariant or a finite verified
transducer.  Establishing that closure is the next route to a genuine
nonhalting certificate.
