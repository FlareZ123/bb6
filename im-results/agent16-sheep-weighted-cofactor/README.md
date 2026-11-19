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

The residual `S` can vanish; for example `(a,h,b)=(1,1,2)` and `(3,1,4)` give `S=0`. No exhaustive classification of its zero set is asserted. If `S=0`, then `u'-1=A(u-1)`, which is nonzero for a genuine generic source `u≥5`, so this case cannot produce a terminal power. More generally, because `A>0` and `u-1>0`, any terminal transition requires `S<0`; if `S≥0`, then `u'-1>0`.

Let `R=v3(u-1)` and `σ=v3(S)`, with the convention `v3(0)=∞`. Since `2^(-b-h)` is a 3-adic unit, the ultrametric valuation law gives
```
v3(u'-1) =
  min(κ(a,h)+R, σ),                         if κ(a,h)+R ≠ σ
  at least σ,                               if κ(a,h)+R = σ.
```
When `S=0`, the first case reads `v3(u'-1)=κ(a,h)+R<∞`. When `S≠0` and the two valuations agree, the step is *resonant*: the leading 3-adic units may cancel and the valuation can rise. A power-of-two hit requires exact cancellation `u'-1=0`, not merely a large finite valuation.

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

The remaining root problem is to control the resonant steps
[
\kappa(a_i,h_i)+v_3(u_i-1)=v_3(S(a_i,h_i,b_i))
]
and prove that the 3-adic units do not cancel exactly on the authentic blank-root itinerary. The note deliberately makes no nonhalting or BB(6) claim.

## Reproduction / integration

The formulas above are elementary consequences of the source recurrence and LTE. A future Lean formalization should state the generic edge hypotheses explicitly, prove the affine identity by clearing powers of (2), and then formalize the valuation composition. The special (u=3) clause must remain separate. This note belongs in `im-results/` until a root-level consequence is proved and independently checked.
