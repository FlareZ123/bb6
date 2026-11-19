# Weighted 3-adic affine dynamics of the odd cofactor

**Agent16, 19 November 2026. Intermediate result.** This note gives a second-coordinate affine representation of the generic Sheep even-return map. It is not a proof of nonhalting and does not decide the blank-root orbit. Its purpose is to expose an unbounded, history-dependent 3-adic weight that is invisible in a fixed odd-modulus quotient.

## 1. Exact odd-cofactor recurrence

For a generic source, write
[
x=2^a u,qquad a\ge 1,quad u\ge5	ext{ odd}.
]
Let
[
F(x)=x+a+(u-1)/2,qquad
h=v_2(F(x)-1),qquad
v=(F(x)-1)/2^h.
]
The first-even return is
[
y=E(x)=1+3^h v=2^b u',
qquad b=v_2(y),quad u'	ext{ odd}.
]
Directly clearing the denominator in (F(x)-1) gives
[
2^{h+1}v=(2^{a+1}+1)u+2a-3.
]
Consequently, in (mathbb Z_3) (where powers of (2) are units),
[
oxed{quad
u'=A(a,h,b)u+B(a,h,b)
quad}
]
where
[
A(a,h,b)=rac{3^h(2^{a+1}+1)}{2^{b+h+1}},
qquad
B(a,h,b)=rac1{2^b}+
rac{3^h(2a-3)}{2^{b+h+1}}.
]
All denominators are powers of (2), so these are 3-adic integers.

## 2. Exact contraction weight

The 3-adic valuation of the affine slope is
[
kappa(a,h):=v_3(A)
=h+v_3(2^{a+1}+1).
]
If (a) is odd, (a+1) is even and (2^{a+1}+1\equiv2\pmod3), so
[
kappa(a,h)=h.
]
If (a) is even, (a+1) is odd. The LTE identity
[
v_3(2^{a+1}+1)=v_3(2+1)+v_3(a+1)=1+v_3(a+1)
]
then gives
[
oxed{quad
kappa(a,h)=
egin{cases}
h,&a	ext{ odd},\
h+1+v_3(a+1),&a	ext{ even}.
end{cases}
quad}
]
Thus every generic edge with (h>0) is strictly 3-adically contracting; so is every edge with even source valuation (a), even when (h=0). The only noncontracting generic edges are precisely
[
a	ext{ odd},qquad h=0.
]

For a finite generic branch word (w=(a_i,h_i,b_i)_{i=0}^{n-1}), composition gives
[
u_n=A_wu_0+B_w,
qquad
v_3(A_w)=K(w):=sum_{i=0}^{n-1}kappa(a_i,h_i).
]
This is an exact weighted-history statement: modulo (3^{K(w)}), the final odd cofactor is independent of the initial odd cofactor (u_0). The special cofactor-three source (u=3) uses the machine's separate (F(x)=x+a+3) clause; it is not a generic affine edge and can be treated as a reset rather than assigned this slope.

## 3. Residual recurrence around the terminal value

The terminal condition for a generic output is (u'=1). Subtracting (1) from the affine recurrence yields
[
u'-1=A(u-1)+2^{-b-h}S(a,h,b),
]
where
[
oxed{quad
S(a,h,b)=3^h(2^a+a-1)-2^h(2^b-1).
quad}
]
The identity follows by collecting (A+B-1); it is exact over the rationals and hence in (mathbb Z_3).

The zero set is in fact completely classifiable.

### Complete classification of the zero residual

**Proposition.** For integers a ≥ 1, h ≥ 0, and b ≥ 1,
S(a,h,b) = 0 if and only if (a,h,b) = (1,1,2) or (3,1,4).

**Proof.** Put M = 2^a + a - 1. The equation S = 0 is
3^h M = 2^h (2^b - 1).
Taking 2-adic valuations gives h = v₂(M). If a = 1, then M = 2, so h = 1 and the equation gives 2^b = 4, hence b = 2.

Now let a ≥ 2. Since 2^a < M < 2^(a+1), we have h < a. Therefore M is congruent to a - 1 modulo 2^(h+1), so h = v₂(a - 1). Write a - 1 = 2^h q, with q a positive odd integer. Then
2^b = 1 + 3^h(2^(a-h) + q)
    = 3^h 2^(2^h q + 1 - h) + 3^h q + 1.

If h = 0, this reduces to 2^b = 2^a + a, strictly between 2^a and 2^(a+1), impossible.

Suppose h ≥ 1, and put A = 2^h q + 1 - h = a - h. Whenever
3^h q + 1 < 2^A,
the displayed equation gives
3^h < 2^(b-A) < 3^h + 1,
which is impossible because the middle term is an integer power of two.

The inequality holds in all cases except two small pairs:
- If h = 1 and q ≥ 3, then 3q + 1 < 2^(2q), by induction from q = 3.
- If h = 2 and q ≥ 3, then 9q + 1 < 2^(4q-1), by induction from q = 3.
- If h ≥ 3 and q ≥ 1, then 3^h q + 1 < 2^(2^h q + 1 - h). For q = 1, h = 3 this is 28 < 64; induction in q multiplies the right side by 2^(2^h), and induction in h at q = 1 multiplies it by 2^(2^h-1), while the left side grows by a factor less than three.

For the two exceptions, direct substitution finishes the proof. If (h,q) = (1,1), then a = 3 and 2^b = 3·2^2 + 3 + 1 = 16, so b = 4. If (h,q) = (2,1), then a = 5 and 2^b = 9·2^3 + 9 + 1 = 82, not a power of two. Thus only the two stated triples occur. □

**Exact source cylinders.** On a genuine generic source x = 2^a u, u ≥ 5 odd, these two cases have the following equivalent 2-adic descriptions:
- a = 1: (h,b) = (1,2) if and only if u ≡ 1 (mod 32), and u' = (15u + 1)/16.
- a = 3: (h,b) = (1,4) if and only if u ≡ 1 (mod 128), and u' = (51u + 13)/64.

In both cases A is respectively 15/16 or 51/64, so v₃(A) = 1. Consequently every genuine S = 0 edge is nonhalting and satisfies the exact valuation update
v₃(u' - 1) = v₃(u - 1) + 1.
Thus the singular σ = v₃(S) = infinity case is not an unresolved branch: it consists of precisely these two contracting cylinders. More generally, because A > 0 and u - 1 > 0, any terminal transition requires S < 0; if S ≥ 0 then u' > 1.

A separate exact BigInt replay of the authentic even orbit through 100,000 returns found 3,389 zero-residual edges: 3,180 of type (1,1,2) and 209 of type (3,1,4). This is finite diagnostic evidence only; the proposition above is the all-parameter proof.

Let `R=v3(u-1)` and `σ=v3(S)`, with the convention `v3(0)=∞`. Since `2^(-b-h)` is a 3-adic unit, the ultrametric valuation law gives
```
v3(u'-1) =
  min(κ(a,h)+R, σ),                         if κ(a,h)+R ≠ σ
  at least σ,                               if κ(a,h)+R = σ.
```
The zero-residual classification above shows that `S=0` always has `κ=1` and gives `R'=R+1`. When `S≠0` and the two valuations agree, the step is *resonant*: the leading 3-adic units may cancel and the valuation can rise. A power-of-two hit requires exact cancellation `u'-1=0`, not merely a large finite valuation.

### Exact normalization of a nonzero resonant step

Suppose (S\ne0) and (\kappa+R=\sigma). Define the integers
[
t=v_3(2^{a+1}+1),\qquad
P=\frac{2^{a+1}+1}{3^t},\qquad
W=\frac{u-1}{2\cdot3^R},\qquad
S_0=\frac{S}{3^\sigma}.
]
Then (P) and (S_0) are 3-adic units, and the exact integer residual identity gives
[
\boxed{\quad
u'-1=\frac{3^\sigma}{2^{b+h}}(PW+S_0).
\quad}
]
Therefore
[
v_3(u'-1)=\sigma+v_3(PW+S_0),
]
with (v_3(0)=\infty). In particular, a terminal power is reached **if and only if**
[
PW+S_0=0.
]
The first additional 3-adic digit cancels exactly when (PW+S_0\equiv0\pmod3). This replaces the vague resonant-unit condition by one explicit integer sum; it also gives every finite valuation gain, not just a lower bound.

The 100,000-return BigInt replay had 29,211 nonzero resonant steps. Exactly 12,441 had (PW+S_0\equiv0\pmod3); the observed excess valuations (v_3(PW+S_0)) ranged up to 12, and none of the 29,211 sums was zero. This is finite diagnostic evidence, not an all-time root argument.

### Calibration against an existing infinite terminal-source family

The normalized sum is **not** nonzero for all generic sources. Agent14's [r29 Z-family construction](../agent14-sheep-r29-hensel-corridor/README.md) gives an explicit infinite family on which it vanishes identically.

For every (k\ge0), put
[
j=507384+1102248k=162(3132+6804k),\qquad
v=\frac{2^{j+4}-259}{3483},\qquad x=64v.
]
Agent14's source calculation gives a genuine generic edge with ((a,h,b)=(6,3,j)) and (E(x)=2^j). Here
[
t=v_3(2^7+1)=1,quad P=43,quad \kappa=4.
]
Since (j) is divisible by 162 and (operatorname{ord}_{243}(2)=162), we have (2^j\equiv1\pmod{243}). Thus
[
S=3^3(2^6+6-1)-2^3(2^j-1)=1871-8\cdot2^j
]
has (v_3(S)=4). Also
[
v-1=\frac{2^{j+4}-3742}{81\cdot43}\not\equiv0\pmod3,
]
so (R=v_3(v-1)=0) and the edge is resonant with (\sigma=\kappa+R=4).

For (W=(v-1)/2) and (S_0=S/81), direct simplification gives
[
43W=\frac{2^{j+4}-3742}{162}
=\frac{8\cdot2^j-1871}{81}
=-S_0.
]
Hence (PW+S_0=0) for every member of this infinite family, exactly as the terminal-edge criterion requires.

This is a useful calibration, not a blank-root hit: the family consists of synthetic ancestors constructed by Agent14. It shows that no claim of the form “the normalized resonant sum is nonzero for every generic source” can be true. The remaining question is specifically whether the authentic orbit from 10 can enter any such exact zero-sum source.

### The h = 0, a = 2 corridor resets the cofactor coordinate

For every generic edge with (a=2) and (h=0), write (x=4u). Then
[
E(x)=F(x)=\frac{9u+3}{2},\qquad
E(x)+12=\frac98(x+12).
]
This is exactly the forward form of Agent14's inverse step (P(y)=(8y-12)/9): each such edge increases (v_3(x+12)) by exactly two.

The odd-cofactor coordinate behaves oppositely. Here
[
\kappa=2,qquad S=6-2^b\not\equiv0\pmod3,
]
so (sigma=v_3(S)=0), strictly below (kappa+R) for every (Rge0). The step is never resonant and the valuation law gives
[
v_3(u'-1)=0.
]
Thus every (a=2,h=0) P-edge resets the target odd-cofactor distance from 1 to valuation zero, even while the separate coordinate (x+12) gains two powers of three. The two 3-adic coordinates track genuinely different aspects of the inverse corridor. This is a local edge theorem, not a global root obstruction.

## 4. Blank-root prefix illustration

The first generic root edges are
[
10\to28\to244\to276\to312\to334\to418\to784.
]
Their source data ((a,h,b)) and weights (kappa) are:

| source | ((a,h,b)) | (kappa) |
|---:|---:|---:|
| 10 | (1,2,2) | 2 |
| 28 | (2,5,2) | 7 |
| 244 | (2,0,2) | 2 |
| 276 | (2,0,3) | 2 |
| 312 | (3,0,1) | 0 |
| 334 | (1,0,4) | 0 |
| 418 | (1,1,4) | 1 |

The cumulative slope valuation after these seven edges is (K=14). In particular, the dependence on the initial cofactor (u_0=5) has disappeared modulo (3^{14}) from the composed affine expression for the final odd cofactor.

## 5. What this does and does not establish

This coordinate change gives a 3-adic contraction weight
[
K_n=\sum_{i<n}\big(h_i+v_3(2^{a_i+1}+1)\big)
]
for the authentic generic branch history. It is not a fixed-modulus invariant: the modulus grows with the actual branch history. It therefore provides a possible route around finite odd-modulus and bounded-history obstructions, but it does **not** by itself show that the root's odd cofactor differs from (1).

The remaining generic root problem is to control only the nonzero resonant steps
[
\kappa(a_i,h_i)+v_3(u_i-1)=v_3(S(a_i,h_i,b_i))
]
and prove that the 3-adic units do not cancel exactly on the authentic blank-root itinerary. The note deliberately makes no nonhalting or BB(6) claim.

## Reproduction / integration

The formulas above are elementary consequences of the source recurrence and LTE. A future Lean formalization should state the generic edge hypotheses explicitly, prove the affine identity by clearing powers of (2), and then formalize the valuation composition. The special (u=3) clause must remain separate. This note belongs in `im-results/` until a root-level consequence is proved and independently checked.
