# Coq TM63 halt itinerary and the Lean terminal-wrapper interface

This note connects the initial blank-root witness to the exact `m1,n1` source specialized by Agent 48's terminal wrapper. It is an integration derivation from the Coq TM63 proof, not yet a Lean proof of the complete itinerary.

Source: `ccz181078/busycoq`, commit `3f302b87f5fb933c46e97672ffbb6907f373fb6e`, `verify/SOBCv5.v`, TM63 section (roughly lines 10813–10985 and the `halt` proof around 11249).

## 1. Blank-root entry

The Coq `init` lemma reaches
```
S1 3 7 m2 6 0 63
```
The computational root checkpoint in `InitialS1RootWitness.md` gives the corresponding Lean candidate
```lean
run tm2 27959 blank = some (s1Config 3 7 2 6 0 63 29)
```
with a 225-cell finite support. This is not yet a Lean theorem; Agent 48 has been asked to formalize the `fRun` equality and finite/infinite embedding.

## 2. First Rsts1 / Rst1' cycle

Coq `Rsts1 n len0 b` gives
```
S1 len0 (1+3*n) m2 b 0 (2^b-1)
  -->* S1 len0 0 m1 (st2 (1+3*n) b + (5*n+2)) 0 (t2 (2+3*n) b).
```
At the initial parameters `n=2, len0=3, b=6`, define
```
A1 := st2 7 6 + 12
B1 := t2 8 6.
```
The output is `S1 3 0 m1 A1 0 B1`.

Coq `Rst1' a0 a b` maps
```
S1 a0 0 m1 a 0 b
  -->* S1 (a0+2+a) (((2^(a0+2)-1)*2^a)-1) m2 b 0 (2^b-1).
```
(The displayed outer counter is the simplification of
`((((2^a0-1)*2+1)*2+1)*2^a-1)`.)
With `a0=3, a=A1, b=B1`, set
```
L1 := A1 + 5
N1 := 31 * 2^A1 - 1.
```
The next S1 source is `S1 L1 N1 m2 B1 0 (2^B1-1)`.

## 3. Rsts1_v2 / second Rst1' cycle

Coq `Rsts1_v2` requires `N1 mod 3 = 1` and yields
```
S1 L1 0 m1 A2 0 B2
A2 := st2 N1 B1 + (5*(N1/3)+2)
B2 := t2 (N1+1) B1.
```
Applying `Rst1'` again with `a0=L1, a=A2, b=B2`, set
```
L2 := L1 + 2 + A2
N2 := (2^(L1+2)-1) * 2^A2 - 1.
```
The next source is `S1 L2 N2 m2 B2 0 (2^B2-1)`.

## 4. Final Rsts2H and the m1,n1 terminal source

The Coq proof then applies `Rsts2H`, whose premise is `N2 mod 3 = 2`. Put
```
k := (N2-2)/3.
```
The underlying `Rsts2 k L2 B2` decomposes as follows.

First, `Rsts` with `a0=2`:
```
S1 L2 (2+3*k) m2 B2 0 (2^B2-1)
  -->* S1 L2 2 m2 A3 0 B3
A3 := st2 (3*k) B2 + 5*k
B3 := t2 (1+3*k) B2.
```

Then `Rst2`:
```
S1 L2 2 m2 A3 0 B3
  -->* S1 L2 1 m1 (A3+B3+2) 0 (2^B3-1).
```
Thus the exact source parameters for Agent 48's m1,n1 terminal wrapper are
```
aTerm := A3 + B3 + 2
bTerm := 2^B3 - 1
LTerm := L2.
```
The wrapper's **pre-drain** prefix endpoint is
```lean
s1Config L2 0 0 (aTerm+bTerm+2) (2^bTerm-1) 0 h'
```
with the outer marker/counter context now `m0,n0`. This is the first phase of Coq's final `Rst1` (`LC_Inc`); the Lean terminal wrapper then discharges the separate `Incs0` drain using `S1CountedDrain`, before applying the source-certified terminal section. The full Coq `Rst1` endpoint after that drain is `S1 L2 0 m0 (aTerm+bTerm+2) 0 (2^bTerm-1)`.

Finally Coq applies `Rst0'` to halt. This identifies the precise interface: initial root witness → both Rsts1/Rst1' stages → final Rsts/Rst2 → Agent 8's m1,n1 pre-drain prefix → Agent 48's counted drain + terminal section.

## 5. Parity / mod-3 side conditions

The recurrences are
```
t2 0 b = b
t2 (j+1) b = 2^(t2 j b)-1
st2 n b = sum_{j=0}^n t2 j b.
```
For `b≥1`, every `t2 j b` with `j≥1` is odd.

- `A1=st2 7 6+12` is odd: one even term (`t2 0 6=6`) plus seven odd terms. Hence `L1=A1+5` is even.
- `N1=31*2^A1-1` is odd and `N1 ≡ 2^A1-1 ≡ 1 (mod 3)`. Since `N1` is odd and 1 mod 3, `N1/3` is even.
- `B1=t2 8 6` is odd. `st2 N1 B1` sums `N1+1` even-many odd terms, so `A2` is even. Thus `L2=L1+2+A2` is even.
- `N2=(2^(L1+2)-1)*2^A2-1` is odd and `N2 ≡ -1 ≡ 2 (mod 3)`, because `L1+2` is even. Hence `N2 ≡ 5 (mod 6)` and `k=(N2-2)/3` is odd.
- `B2=t2(N1+1)B1` is odd. Since `k` is odd, `st2(3*k)B2` sums `3*k+1` even-many odd terms, so `A3` is odd. `B3=t2(1+3*k)B2` is odd.
- Therefore `aTerm=A3+B3+2` is even and `bTerm=2^B3-1` is odd.

This supplies the two Coq `rw_mod` obligations (`N1 mod 3=1`, `N2 mod 3=2`) and the parity profile of the final terminal parameters in a form suitable for Lean arithmetic lemmas.

## Status

- The initial root run and finite support are computationally reproduced in JavaScript and recorded separately; not yet Lean-formalized.
- The parameter chain above is a direct algebraic reading/simplification of the Coq macro statements; the Lean composition of the full itinerary remains open.
- The final m1,n1 pre-drain endpoint is the correct input to the Agent 48 terminal wrapper; do not confuse it with the full post-`Incs0` Coq Rst1 endpoint.
