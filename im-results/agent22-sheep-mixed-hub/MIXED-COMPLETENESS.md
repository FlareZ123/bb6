# All even moduli: the synthetic Sheep even-return quotient is strongly connected

**Agent 22 | R010 | 2026-11-03.** This extends [the all-power-of-two inverse-word theorem](./DYADIC-COMPLETENESS.md) to **every even modulus**. The proof is an explicit finite construction using the published Sheep return formula, modular inverses, the Chinese remainder theorem, and a strong-induction lemma on the multiplicative order of 2. It has been checked on a substantial independent exact-integer corpus. It has **not** yet been independently peer-reviewed or kernel-formalized as a whole, and neither theorem decides the authentic blank-start Sheep orbit or BB(6).

## Theorem and exact meaning

Let `m=2^p q` with integers `p>=1`, `q>=1` odd. Vertices of the directed quotient `G_m` are the **even** residues modulo `m`. An edge `r -> s` exists when there are positive integers `x,z` such that

```
x ≡ r (mod m),       z ≡ s (mod m),
x = 2^a u,           a>=1, u odd >=5,
F(x) = x+a+(u-1)/2,  E(x)=z,
```

where `E` is the genuine *first-even* return, including any necessary generic odd-section returns from `F(x)`. The witnesses can differ for each quotient edge; the graph makes **no assertion** that those witnesses belong to one continuous blank-origin trajectory. We use only the generic u>=5 branch.

**Theorem.** For every even modulus `m`, `G_m` is strongly connected. Every even residue reaches the zero residue in at most `floor(p/2)+1` edges; zero has an edge to every even residue. Consequently the directed diameter is at most `floor(p/2)+2`. For `q=1`, the earlier pure-dyadic theorem gives the sharper `floor(p/2)+1` diameter bound.

The proof has three independent ingredients. All its quantifiers are uniform over unbounded `p,q`.

## Lemma 1: lift any prescribed dyadic inverse edge while fixing the full source residue

From the [dyadic theorem](./DYADIC-COMPLETENESS.md), for any even residue `r2≠0 (mod 2^p)`, we have a canonical path to zero, each edge being of the form

```
r2 = T[p,a,h](s2),   1<=a<p, 0<=h<=p-a-1,
```

with `T` the explicit modular inverse of the generic first-even return, defined in the earlier proof. Set `D=1+2^(a+1)` and `t=p-a-h-1>=0`.

**Lifting claim.** Given **any** full source residue `r (mod m)` reducing to `r2 (mod 2^p)`, there is a real generic first-even transition `x -> z` with

```
x ≡ r (mod m),        z ≡ s2 (mod 2^p).
```

The target's residue modulo odd `q` need not be specified.

**Proof.** As `q` is odd, choose an odd integer `u0>0` by CRT such that

```
u0 ≡ r / 2^a          (mod 2^(p-a)),
u0 ≡ 2^(-a)*r        (mod q).
```

Here the first quotient is well-defined modulo `2^(p-a)` because `r2` has exact valuation `a`, and `2^(-a)` is invertible modulo odd `q`. For every integer `k>=0`, put

```
u(k) = u0 + 2^(p-a)*q*k,
C(k) = D*u(k)+2a-3 .
```

The inverse-residue equality `r2=T[p,a,h](s2)` implies `C(0)` is divisible by `2^(h+1)`. Define `v(k)=C(k)/2^(h+1)`. Then

```
v(k) = v(0) + 2^t*D*q*k,
z(k) = 1+3^h*v(k)
     = z(0) + 2^t*(3^h*D*q)*k .
```

The same inverse equality gives `z(0)≡s2 (mod 2^t)`. Since `3^h D q` is odd, it is invertible modulo `2^(p-t)`; thus there exists a residue class of `k` modulo `2^(p-t)` for which `z(k)≡s2 (mod 2^p)`. The specified `s2` is even, which ensures `v(k)` is odd. Adding multiples of `2^(p-t)` to `k` makes `u(k),v(k)>=5` while preserving all congruences and parity.

Now let `x=2^a u(k)`. It has the required full source residue; direct algebra gives `F(x)=1+2^h v(k)`, and the authentic odd-block formula gives `E(x)=1+3^h v(k)=z(k)`. This proves the edge. The argument includes the terminal case `t=0`: in that case the oddness of `v(k)` is imposed by the even target.

**Consequence:** Any canonical dyadic path from `r mod 2^p` to zero can be lifted step by step from **any given even source residue modulo `m`**. The odd residue of each new target is whatever its constructed witness produces. After at most `floor(p/2)` such edges, we reach some full residue divisible by `2^p`.

## Lemma 2: every dyadic-zero source residue has a one-step edge to full zero

We first establish an elementary number-theoretic statement that avoids assumptions about the odd cofactor `q`.

**Multiplicative-order descent lemma.** For every odd `q>=1`, any integer `r`, and any lower bound `A`, there exists an arbitrarily large positive `a>=A` satisfying

```
(2+2^(-a))*r +2a-1 ≡ 0 (mod q).
```

The inverse power of 2 is interpreted in the unit group modulo odd `q`.

**Proof by strong induction on q.** For `q=1`, every `a` works. Suppose `q>1`, and let `P=ord_q(2)`, the positive multiplicative order of 2 modulo `q`. Euler's theorem gives `1<=P<=phi(q)<q`. Define `d=gcd(P,q)`, a positive **odd** divisor of `q`, satisfying `d<q`. By the induction hypothesis for modulus `d`, choose a nonnegative `c` such that

```
f(c)=(2+2^(-c))*r+2c-1 ≡0 (mod d).
```

In the equation above, reducing the inverse power from modulus `q` to `d` is valid because `d|q`. For any integer `k`, the multiplicative order identity yields

```
f(c+kP) ≡ f(c)+2kP (mod q).
```

Because `q` is odd, `gcd(2P,q)=gcd(P,q)=d`. Hence the linear congruence `2kP≡-f(c) (mod q)` is solvable: its right-hand side is divisible by `d`. One may increase `k` by arbitrary multiples of `q/d` to make `a=c+kP>=A`. This completes the induction.

**One-step conclusion.** Let `r` be an even full residue with `r≡0 (mod 2^p)`. By the descent lemma choose `a>=p` satisfying the congruence with this `r`. Use CRT again to choose an odd integer `u>=5` such that

```
u ≡ 2^(-a)*r       (mod q),
u ≡ 1-2a          (mod 2^(p+1)).
```

Put `x=2^a u`. Since `a>=p`, `x≡r (mod 2^p)`; the first congruence also gives `x≡r (mod q)), so `x≡r (mod m)`. The generic return satisfies

```
2 F(x) = (2^(a+1)+1)*u + 2a-1.
```

Modulo `q`, this is `(2+2^(-a))*r + 2a-1 ≡0`; modulo `2^(p+1)`, the second congruence makes `F(x)≡0 (mod 2^p)`. Since `p>=1`, `F(x)` is even, so `E(x)=F(x)≡0 (mod m)`. The source is generic and positive. Thus every dyadic-zero full residue has a **single genuine edge to the full zero residue**.

## Lemma 3: zero has an edge to every even target residue

This is already covered by `SheepMixedHub.lean` for arbitrary `q`. An especially compact witness for any even `s (mod m)` is:

```
u = 5q,                 c=(u-1)/2,
a = p + ((s-p-c) mod m),
x = 2^a*u,              F(x)=x+a+c.
```

Here `u` is odd and at least 5, `a>=p`, and `x≡0 (mod m)`. By construction `F(x)≡s (mod m)`. As `s` is even and the modulus `m` is even, `F(x)` is already even, so `E(x)=F(x)`. Thus zero has a one-step outgoing edge to every even residue.

Combining Lemmas 1–3 yields the stated strong connectivity and diameter bound.

## Reproducibility and limits

- `verify_mixed_complete.py` is a deterministic Python 3 checker and explicit constructor for all three lemmas. It implements the multiplicative-order descent recursively through `gcd(q,ord_q(2))`; performs all CRT lifts with exact integer arithmetic; and independently replays `F` one section transition at a time through every odd block, comparing against `E`.
- An earlier implementation of the same arithmetic construction checked all **54,315** even classes for `p=1,...,8` and odd `q∈{1,3,5,7,9,11,13,15,21,25,27,31,45}`, with **149,739** witnessed mixed path edges. It separately checked a zero-to-every-even-target witness for each modulus. The upgraded repository script adds explicit literal-`F` odd-block replay; rerun it to audit the final published version. No finite enumeration is used as a premise of the unbounded proof.
- Source alignment: the original six-state Sheep table is `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`. Agent16's `EvenSourceBridge.lean`, successful source CI [41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547), establishes complete original-machine halting equivalence to a true even-orbit power-of-two hit. The new quotient result uses its exact published one-variable dynamics, without modifying that semantic source.
- The standalone **zero outgoing hub** theorem was Lean-checked under standard axioms; the all-even-moduli theorem in this file currently has a detailed mathematical proof and exact witness code rather than an all-parameter Lean certificate. Peer validation and an independent source-level proof audit remain worthwhile.
- **This is a theorem about the synthetic quotient transition graph.** The witness for one residue-edge may have a different full integer section state from the witness for the next edge, so the quotient path cannot be concatenated into a genuine unmodified-Turing-machine orbit. It does not prove that the Sheep blank tape visits zero or any other residue, and does not prove a BB(6) value or improve its bound.

**Research consequence.** No nonempty globally inductive property that depends only on the *current* Sheep even-state residue modulo any fixed even modulus can exclude all potential halting-power residues: every such quotient graph is strongly connected. Pure 3-adic quotients had separately been found complete by Agent17. The mixed-modulus theorem closes the finite-residue-only method gap, while leaving real blank-orbit and richer correlated invariants entirely open.
