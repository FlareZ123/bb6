# Exact finite modular minimization for odd-depth Machine C high stopping residuals

**Status (21 November 2026):** The exact finite modular minimization, logarithmic cutoff, uniform sharp envelope, the stronger uniform residual wall `4*(3*m+1)*(Y+2) >= 35*2^(2*m+2)-35-24*m` for odd `m>=3`, the root-sensitive dyadic gap, and the M8-filtered logarithmic bound have paper proofs. The new arithmetic compositions are **not yet Lean-certified**. The original-source stopping/normalization chain is source-certified. The M8 quotient-filter module's compile step completed in existing source workflow run 42367962614, and `#print axioms` reports `[propext, Classical.choice, Quot.sound]` for `affineQuotientExcluded_sound` (no `sorryAx`); the new arithmetic compositions are paper-level. No complete Machine C or BB(6) decision is asserted.

Let m≥1 be odd, j,k,d,Y natural, and suppose

```
k+j+3*m+5 = 2^(2*m+2)*(j+3),
2^d*(Y+2) = k+2,
Y%12 = 4.
```

Set L=m+1 (even), Q=(2^(2*L)-1)/3 (odd), T=2*L. For each integer t in [0,T), define

```
r_t = (-m * inverse_mod(2^t,Q)) mod Q,  0<=r_t<Q,
v_t = r_t + ((2-r_t) mod 4)*Q.
```

The modular inverse exists because Q is odd, and Q≡1 mod4 because L≥2. No v_t can be zero: v_t≡2 mod4. The direct definition has T=2m+2 candidates, but the logarithmic-cutoff theorem below proves that a minimizer always has 2^t≤6m, reducing the exact search to at most floor(log2(6m))+1 candidates. Then **the following is a rigorous universal necessary bound**:

```
Y >= min_(0<=t<T) (3*v_t-2).                      (★)
```

The RHS can be evaluated using at most **floor(log2(6*m))+1 power-of-two residue operations**, independent of j,k,d and their magnitudes. It is the smallest nonnegative right counter compatible with these *necessary modular conditions*. Further source equations could rule out even that minimum; (★) does not guarantee genuine blank reachability or original stopping-state ancestry.

## Proof

From the high stopping equation, `k+2=(2^(2L)-1)*(j+3)-3m=3(Q*(j+3)-m)`. As `2^d` is coprime to three, the scale equation forces `3|(Y+2)`; since `Y≡4(mod12)`, write `Y+2=3v` for v>0 with v≡2(mod4). Dividing the scale identity by 3 yields

```
v*2^d + m = Q*(j+3).
```

In particular `v*2^d≡-m(modQ)`. Since `2^T=2^(2L)=3Q+1`, powers of two mod Q have period dividing T, so t=d modT satisfies `v≡-m(2^t)^(-1)(modQ)`. This is `v≡r_t(modQ)`. Because Q≡1(mod4), all simultaneous solutions of `v≡r_t(modQ)` and `v≡2(mod4)` are `v=v_t+4Qh` for integers h. Their least positive nonnegative representative is the displayed v_t. Thus v≥v_t for the actual t, whence Y=3v-2≥3v_t-2≥min_t(3v_t-2). All steps use exact arithmetic; no dynamic simulation.

## Uniform envelope and infinite sharpness

The finite minimum (★) has a simple uniform lower envelope. Under the same hypotheses,

```
(3*m+1)*(Y+2) >= 2^(2*m+3) - 6*m - 2.
```

Equivalently, with `Q=(2^(2*m+2)-1)/3` and `v=(Y+2)/3`,

```
v >= 2*(Q-m)/(3*m+1),
Y >= 3*ceil(2*(Q-m)/(3*m+1))-2.
```

This is a `4^m/m`-scale lower bound. On the source-certified deep sector, where `Y%12=4`, it strictly strengthens the earlier source-certified `2^(m+2)-6*m-1` bound for every odd `m>=1`. It is still a necessary condition on the normalized residual, not a blank-root decision.

### Proof of the envelope

Put `L=m+1`, `Q=(2^(2*L)-1)/3`, and `Y+2=3*v`. The last identity and `Y%12=4` give `v%4=2`. The stopping equation and affine scale give

```
v*2^d + m = Q*(j+3),       2^(2*L)=3*Q+1.
```

Reduce `d` modulo `2*L`, writing `t=d%(2*L)`. Then `Q | v*2^t+m`; set `n=(v*2^t+m)/Q`. For `t<=2*L-2`, the congruence `v%4=2` gives

```
n*Q = v*2^t+m = m+2^(t+1)  (mod 2^(t+2)).
```

Since `3*Q=2^(2*L)-1`, the inverse of `Q` modulo `2^(t+2)` is `-3`. Hence

```
n = 2^(t+1)-3*m  (mod 2^(t+2)).
```

If `2^(t+1)<=3*m+1`, use `n>=1` to obtain `v>=(Q-m)/2^t >= 2*(Q-m)/(3*m+1)`. Otherwise `2^(t+1)-3*m` is the least positive residue, so

```
v >= ((2^(t+1)-3*m)*Q-m)/2^t
  = 2*Q-(3*m*Q+m)/2^t
  > 2*(Q-m)/(3*m+1),
```

where the final inequality uses `2^t>(3*m+1)/2`.

For the remaining residue `t=2*L-1`, let `A=2^(2*L)`. Here `n` is odd, and reduction modulo `2*A` in `n*(A-1)=3*(v*2^(2*L-1)+m)` gives `n=-3*m (mod 2*A)`. Since `0<3*m<2*A`, `n>=2*A-3*m`; substituting in `v=(n*Q-m)/(A/2)` gives `v>Q`, which is stronger than the claimed bound. Multiplying the bound for `v` by three and substituting `Q=(2^(2*L)-1)/3` proves the displayed inequality.

### Logarithmic cutoff for the exact finite minimum

For `0<=t<=2*L-2`, the same quotient argument gives the exact representative without a modular inverse:

```
n_t = the least positive residue of (2^(t+1)-3*m) modulo 2^(t+2),
v_t = (n_t*Q-m)/2^t.
```

The numerator is divisible by `2^t` and `v_t%4=2`; this is exactly the least positive CRT solution in (★), because every admissible quotient is `n_t+h*2^(t+2)` with `h>=0`, and `v` increases with that quotient.

Moreover, **no minimizing exponent residue has `2^t>6*m`**. For such a `t` (still assuming `t<=2*L-2`), `n_t=2^(t+1)-3*m`, and

```
v_t = 2*Q-(3*m*Q+m)/2^t > 3*Q/2-1/6 > Q.
```

The endpoint `t=2*L-1` also has `v_t>Q`, by the endpoint congruence in the envelope proof. On the other hand, let `t0=floor(log2(3*m))`. It lies in `0..2*L-2`, and `n_t0=2^(t0+1)-3*m` satisfies `0<n_t0<2^t0`; hence `v_t0<Q`. Therefore the exact minimum is attained among only

```
0 <= t <= floor(log2(6*m)).
```

This reduces the exact minimization from `2*m+2` candidates to `floor(log2(6*m))+1` candidates and replaces modular inversion modulo the large `Q` by a single residue modulo a power of two. It is an exact reduction, not a heuristic or a finite-depth approximation.

### The envelope is sharp for infinitely many genuine source-normalized inputs

For every `r>=1`, take

```
m=(4^r-1)/3,   t=2*r-1,   L=m+1,   Q=(2^(2*L)-1)/3,
v=(Q-m)/2^t,   d=t+2*L,
j=3*v*2^t-2,  k=3*v*2^d-2,  Y=3*v-2.
```

Because `3*m+1=2^(t+1)` and `t+2<=2*L`, the identity `3*Q=2^(2*L)-1` gives `Q-m=2^(t+1) (mod 2^(t+2))`. Thus `v` is an integer with `v%4=2`. Also `m%4=1`, `j%4=2`, so `j` is even and `(j+m)%4=3`. Direct substitution using `v*2^t=Q-m` and `2^(2*L)=3*Q+1` verifies both the original second stopping equation and `2^d*(Y+2)=k+2`.

These parameters therefore lie in the exact deep sector of the original source. The already source-certified `second_halt_deep_sector` and `second_deep_affine_terminal_four_mod_twelve` give the actual unbounded `affineNormalize` output with right residual congruent to four modulo twelve and the same scale identity. Since `k+2=3*v*2^d` has 2-adic valuation `d+1`, while every such source residual plus two has 2-adic valuation one, that source normalization must have depth `d` and residual exactly `Y`. The displayed envelope is therefore attained by genuine source-normalized stopping inputs for infinitely many odd `m` (not merely by abstract modular representatives). The source-normalizer identification is now drafted in `M8SharpFamily.lean` as part of `m8SharpFamily_unreachable`; the draft has not yet passed local preflight or source CI.

The first two instances are:

| `r` | `m` | `j` | `k` | normalized `Y` |
|---:|---:|---:|---:|---:|
| 1 | 1 | 10 | 190 | 4 |
| 2 | 5 | 4,078 | 16,711,678 | 508 |

The `r=1` case is the existing right-four tower; `r=2` shows that the exact `m=5` lower bound 508 is attained at an actual source-normalized stopping input. Neither example is asserted to be blank-reachable.

### A root-sensitive gap beyond the sharp envelope

Write \(A=3m+1\). The exact CRT residues, combined with the M8 quotient
filter in the dyadic case, give a stronger closed-form wall than the
uniform envelope. For every odd \(m\ge3\), any blank-root-reachable
deep-sector stopping input satisfies

\[
4Av\ge35Q-8m,
\qquad
4(3m+1)(Y+2)\ge35\cdot2^{2m+2}-35-24m,
\]
where \(v=(Y+2)/3\) and \(Q=(2^{2m+2}-1)/3\). This is a necessary
condition on the actual source-normalized residual, not a reachability
decision. In the non-dyadic case it follows already from the raw CRT
minimum; the M8 exclusion is essential in the dyadic exceptional case.

If \(A\) is not a power of two, the proof below establishes this
inequality without using the M8 correction. If \(A\) is a power of
two, then \(A=4^r\), since \(A\) is even and
\(A\equiv1\pmod3\). For every \(r\ge1\), the exact
M8-filtered minimum is stronger:

\[
Av\ge(A+1)Q-m,
\qquad
Y\ge2^{2m+2}+\frac{2^{2m+2}}{A}-4.
\]

At \(r=1\), this is \(m=1\), \(A=4\), \(Q=5\). The four
raw CRT minima for \(t=0,1,2,3\) are respectively \(14,2,6,18\).
The \(t=1\) value \(v=2\) satisfies the M8-forbidden parity cylinder,
whereas \(t=2\) has \(v=6\); hence the exact filtered minimum is
\(v\ge6\), or \(Y\ge16\). The infinite sharp family developed below
is the subfamily \(r\ge2\).

#### Non-power-of-two case

Assume \(m\ge3\) is odd and \(A\) is not a power of two.
Let \(s\) be the least integer with \(2^s>A/2\). Then
\(2^s\le A<2^{s+1}\) and \(s\ge3\). For each
\(t<s\), let \(n_t\) be the least positive residue of
\(2^{t+1}-3m\) modulo \(2^{t+2}\). It is positive and odd, and

\[
v_t=\frac{n_tQ-m}{2^t}.
\]

Also \(2^t\le A/2\), so \(A/2^t\ge2\). Split into three
cases.

1. If \(n_t=1\), then \(A=2^{t+1}w\) for an odd
   \(w\). Since \(A\) is not a power of two, \(w>1\);
   and \(A\equiv1\pmod3\) forces \(3\nmid w\).
   Thus \(w\ge5\), so
   \(Av_t=2w(Q-m)\ge10(Q-m)\).

2. If \(n_t=3\), then \(A+2=2^{t+1}w\) for a positive
   odd \(w\) divisible by three, since \(A+2=3(m+1)\).
   For \(t\ge1\), this gives
   \(A/2^t=2w-2/2^t\ge5\); for \(t=0\),
   \(m\ge3\) forces \(w\ge7\), so the same lower
   bound holds. Hence \(Av_t\ge5(3Q-m)\).

3. Otherwise, since \(n_t\) is positive and odd,
   \(n_t\ge5\). Therefore
   \(Av_t=(A/2^t)(n_tQ-m)\ge10Q-2m\).

Each of these three bounds is at least \(35Q/4-2m\). For the first,
use \(Q\ge7m\), which follows from
\(4^{m+1}-1\ge21m\) for \(m\ge3\); the other two
comparisons are immediate.

For \(s\le t\le2L-2\), the least residue is now the positive
integer \(n_t=2^{t+1}-3m\), and

\[
v_t=2Q-\frac{3mQ+m}{2^t}.
\]

Thus \(v_t\) increases with \(t\), so it suffices to bound
\(v_s\). Put

\[
n=n_s=2^{s+1}-3m=2^{s+1}-A+1,
\qquad
z=A/2^s=2-(n-1)/2^s.
\]

The integer \(n\) is positive, odd, and not one (as \(A\) is
not a power of two); also it cannot be three, since that would make
\(2^{s+1}=A+2=3(m+1)\). Hence \(n\ge5\). Since
\(A>2^s\), also \(n\le2^s-1\).

If \(n=5\), then \(A=2^{s+1}-4\). The congruence
\(A\equiv1\pmod3\) forces \(s\) even; as
\(m\ge3\), this gives \(s\ge4\), hence
\(z=2-4/2^s\ge7/4\) and \(zn\ge35/4\).

If \(n\ge7\), consider the concave quadratic

\[
f(n)=n\left(2-\frac{n-1}{2^s}\right).
\]

On \([7,2^s-1]\) its minimum is at an endpoint. For
\(s\ge3\),

\[
f(7)=14-42/2^s\ge35/4,
\qquad
f(2^s-1)=2^s+1-2/2^s\ge35/4.
\]

Thus in either case \(zn\ge35/4\), and

\[
Av_s=z(nQ-m)\ge35Q/4-2m,
\]

because \(z<2\). The endpoint \(t=2L-1\) has
\(v_t>Q\) by the endpoint calculation in the envelope proof,
so it also satisfies the bound. Since every actual \(v\) is at
least its corresponding \(v_t\), the uniform inequality follows
for all non-power-of-two \(A\).

#### Exceptional dyadic case and M8 exclusion

Now let \(A=2^{2r}\), \(r\ge2\), so
\(m=(4^r-1)/3\), \(t_*=2r-1\), and
\(2^{t_*}=A/2\). The uniform envelope is attained uniquely at
\(t=t_*\), \(n_{t_*}=1\), and
\(v_*=(Q-m)/2^{t_*}=2(Q-m)/A\). Every other admissible quotient
is larger.

These parameters admit a division-free closed form. Since
\(Q=(4^L-1)/3\) and \(3m+1=4^r\),

\[
Q-m=4^r\frac{4^{L-r}-1}{3},
\quad
v_*=2\frac{4^{L-r}-1}{3},
\quad
Y_*=2\cdot4^{L-r}-4,
\]
\[
j=4^L-4^r-2,
\quad
k=4^{2L}-4^{L+r}-2,
\quad
d=2r-1+2L.
\]

In particular, \(j+3m+3=4^L=2^{2L}\). These forms are convenient
for formalizing the infinite family without nested natural-number
division.

For this sharp family, \(t_*+3\le2L\); reducing
\(3Q=2^{2L}-1\) modulo \(2^{t_*+3}\) and using
\(3m+1=2^{t_*+1}\) gives
\(Q-m=2^{t_*+1}\pmod{2^{t_*+3}}\). Hence
\(v_*\equiv2\pmod8\) and
\(Y_*=3v_*-2\equiv4\pmod8\). Any actual input with this
exponent residue has source depth \(d=t_*\pmod{2L}\), hence
\(d\) is odd and, because \(r\ge2\),
\(d\ge3\). Its first normalized coordinate \(x\)
satisfies the source mass identity

\[
x+2Y_*+4d=2j+3+2k.
\]

Here \(j\equiv2\pmod4\), \(k\equiv6\pmod8\),
and \(d\) is odd. Therefore \(x\equiv7\pmod8\).
The normalized state lies in the \((7,4)\pmod8\) cylinder
used by \(affineQuotientCondition\) in
`im-results/agent15-c-halting/AffineQuotientExclusion.lean`.
Its existing \(affineQuotientExcluded\_sound\) theorem rules
out \(CReach\) for this state. The source
stopping/normalization theorems are source-certified. The quotient-filter
module's compile step completed in workflow 42367962614, which failed
later at an unrelated missing `HighZeroEven.lean` path; its exported
axiom profile is `[propext, Classical.choice, Quot.sound]` with no
`sorryAx`. The arithmetic family-to-cylinder composition is now
drafted in `M8SharpFamily.lean` as
`m8SharpFamily_unreachable`, importing the generic wrapper above,
but neither new file has yet passed local preflight or source CI.

The M8 correction removes \(v_*\) at \(t=t_*\). For
\(t<t_*\), write \(s=t_*-t\ge1\). The least positive
residue is \(n_t=A/2^s+1\), whence
\(v_t=2Q+2^{s+1}(Q-m)/A>2Q\). At \(t=t_*\), the next
CRT solution is \(v_*+4Q>2Q\). For \(t>t_*\), the
raw-residue quotient increases with \(t\); the first value, at
\(t=t_*+1\), is \( ((A+1)Q-m)/A<2Q\). This candidate
is not M8-excluded because \(t_*+1\) is even while
\(m+1\equiv2\pmod4\). The endpoint \(t=2L-1\)
has \(v>3Q\). Thus the exact minimum after the M8 correction
is attained at \(t_*+1\), and every blank-root-reachable input
in this exceptional family satisfies the displayed stronger
inequality. With \(B=2^{2m+2}\), the raw residual minimum is
\(Y_{raw}=2B/A-4\), while the M8-filtered floor is
\(Y_{M8}=B+B/A-4\). Hence the shifted floors satisfy the exact
identity \( (Y_{M8}+4)/(Y_{raw}+4)=(A+1)/2=(3m+2)/2\).
Thus the quotient cylinder raises the necessary residual floor by an
exact linear-in-`m` factor along the entire infinite sharp family
(without claiming the filtered minimum is itself reachable).

Sample quotient lower bounds (before rounding \(Y\) to
\(4\pmod{12}\)):

| \(m\) | case | lower bound on \(v\) | exact modular minimum \(v\) |
|---:|---|---:|---:|
| 3 | nonexceptional | 74 | 74 |
| 5 | exceptional, root-reachable | 1,450 | 170 (M8-excluded) |
| 7 | nonexceptional | 8,690 | 15,018 |
| 9 | nonexceptional | 109,226 | 109,226 |
| 21 | exceptional, root-reachable | 5,955,687,983,786 | 183,251,937,962 (M8-excluded) |

These bounds sharpen the residual frontier but still leave the general
blank-root classification open.

#### The dyadic family survives the maintained parameter-only high sieve

The infinite family above is not already removed by Agent 19's current
`highAllowed` predicate. Its exact identities give
```
j+3*m+3 = 2^(2*L),
j%4=2,  j%8=6,  m%4=1,  m%8=5.
```
Moreover, `m%32=5` when `r=2`, and `m%32=21` for every `r>=3`;
similarly `j%32=14` when `r=2`, and `j%32=30` for every `r>=3`.
Thus `(j+m)%32=19` in every case. These residues defeat all five
`jointHighAllowed` clauses and the additional `m%32=5, j%32=12`
rectangle. The four Agent 19 odd-special filters all require
`j%8∈{7,3,5,1}`, whereas this family has `j%8=6`. Finally, for every
`n` admitted by the all-depth guard's range `n+4<=2*m+2=2*L`,
`j+3*m+3=2^(2*L)` has residue zero modulo `2^(n+4)`, not the required
`2^(n+2)`. Hence the whole family satisfies the current parameter-only
`highAllowed` predicate while its actual normalized state is in the
source-forbidden M8 cylinder. This is a concrete, infinite nonredundancy
witness for adding the normalized M8 test to the high branch; it does not
decide any of the remaining parameters.

### M8-filtered logarithmic lower bound for blank-root candidates

The M8 quotient cylinder gives a general source-sensitive correction to the modular minimum. In the deep sector, put `v=(Y+2)/3` and `t=d mod (2*L)`. Since `2*L` is even, `d%2=t%2`. The source mass identity is

```
x+2*Y+4*d = 2*j+3+2*k.
```

Together with `j+m=3 (mod 4)`, `k+2=3*v*2^d`, and `Y=3*v-2`, it gives the exact equivalence

```
(x%8=7 and Y%8=4)  <->  (v%8=2 and 2*t = m+1 (mod 4)).
```

Indeed, `Y%8=4` is equivalent to `v%8=2`; in that case `2*Y=0 (mod 8)` and `2*k=4 (mod 8)` for every `d>=1`. If `m%4=1`, then `j%4=2` and the mass identity gives `x%8=7` exactly when `d` is odd. If `m%4=3`, then `j%4=0` and it gives `x%8=7` exactly when `d` is even. These are precisely `2*d=m+1 (mod 4)`, hence `2*t=m+1 (mod 4)`. Because `Y%12=4`, the other three cylinders in `affineQuotientCondition` (whose right coordinates are 2, 15, or 7 modulo 16) cannot apply; M8 is the only quotient cylinder relevant here.

#### A small-residue parity shortcut for the M8 test

For every candidate in the logarithmic search when `m>=3`, `t+3<=2*L`, so `3*Q=2^(2*L)-1` is `-1` modulo `2^(t+3)`. Write the least positive CRT residue as

```
n_t = 2^(t+1)-3*m + q_t*2^(t+2),
q_t = max(0, ceil((3*m-2^(t+1))/2^(t+2))).
```

From `v_t*2^t+m=Q*n_t`, multiplying by 3 and reducing modulo `2^(t+3)` gives

```
3*v_t = -2-4*q_t (mod 8),
v_t = 2+4*q_t (mod 8).
```

Thus the M8 test `v_t%8=2` is equivalent simply to `q_t` being even. The full exclusion test in the logarithmic range can be evaluated as `q_t%2=0` and `2*t=m+1 (mod 4)`, without reducing the large integer `v_t` modulo 8. This is a useful simplification for a Lean implementation.

For each modular exponent residue `t`, let `v_t` be the exact CRT minimum from (★), and define

```
vhat_t = v_t+4*Q,  if (v_t%8=2 and 2*t=m+1 (mod 4)),
         v_t,      otherwise.
```

If the first case holds, the solution `v=v_t` would put the actual normalized state in the source-forbidden M8 cylinder, so it cannot be blank-root reachable. The next solution in that CRT class is `v_t+4*Q`; hence every blank-root-reachable input satisfies `v>=vhat_t` for its exponent residue. Therefore

```
Y >= 3*min_(0<=t<2*L) vhat_t - 2.
```

This is a necessary bound using the existing `affineQuotientExcluded_sound` filter theorem; its exported axiom profile is `[propext, Classical.choice, Quot.sound]` with no `sorryAx`. It is not a complete root decision: the other source constraints may exclude more.

#### The M8-filtered minimum also has a logarithmic cutoff

Let `t0=floor(log2(3*m))`. Both `t0` and `t0+1` lie in `0..2*L-2`, and they have opposite parity. At `t0`, `0<n_t0<2^t0`, so `v_t0<Q`. At `t0+1`, the raw residue is `n=2^(t0+2)-3*m` and

```
v_(t0+1) = 2*Q-(3*m*Q+m)/2^(t0+1) <= 3*Q/2-1/6,
```

because `2^(t0+1)<=6*m`. Exactly one of these two consecutive residues fails the M8 parity condition `2*t=m+1 (mod 4)`; that candidate is not M8-excluded. Thus the M8-filtered minimum is at most `3*Q/2-1/6`.

For `t<=2*L-2` with `2^t>6*m`, the raw-residue formula gives `v_t=2*Q-(3*m*Q+m)/2^t >3*Q/2-1/6`, so such a residue cannot minimize `vhat_t`. The endpoint `t=2*L-1` is even larger: its quotient congruence gives `v_t>=4*Q-(6*m*Q+2*m)/2^(2*L)>3*Q`. Therefore the M8-filtered minimum is attained among only

```
0 <= t <= floor(log2(6*m)).
```

So the source-filtered residual lower bound is still computable in `O(log m)` exact power-of-two residue operations.

An exact evaluator is:

```python
def m8_filtered_lower_bound(m: int) -> tuple[int, int]:
    assert m >= 1 and m % 2 == 1
    L = m + 1
    Q = (2 ** (2 * L) - 1) // 3
    candidates = []
    t = 0
    while 2 ** t <= 6 * m:
        modulus = 2 ** (t + 2)
        n = (2 ** (t + 1) - 3 * m) % modulus
        numerator = n * Q - m
        assert numerator % (2 ** t) == 0
        v = numerator // (2 ** t)
        assert v % 4 == 2
        m8 = (v % 8 == 2) and ((2 * t - (m + 1)) % 4 == 0)
        vhat = v + 4 * Q if m8 else v
        candidates.append((3 * vhat - 2, t))
        t += 1
    return min(candidates)
```

Sample exact lower bounds:

| `m` | raw modular minimum `v` | M8-filtered minimum `vhat` | lower bound on `Y` |
|---:|---:|---:|---:|
| 1 | 2 | 6 | 16 |
| 3 | 74 | 74 | 220 |
| 5 | 170 | 1,450 | 4,348 |
| 7 | 15,018 | 16,382 | 49,144 |
| 9 | 109,226 | 109,226 | 327,676 |
| 11 | 5,417,642 | 5,417,642 | 16,252,924 |
| 13 | 22,369,618 | 22,369,618 | 67,108,852 |
| 21 | 183,251,937,962 | 5,955,687,983,786 | 17,867,063,951,356 |

These are lower bounds after applying the M8 cylinder only; they do not claim that the minimizing filtered residue is itself reachable.

### Relation to the exact finite minimum

The finite minimizer (★) remains sharper for many individual `m`; the new envelope is a closed-form bound valid uniformly for every odd `m` and is exactly sharp on the infinite sequence above. For the sample values already tabulated:

| `m` | raw envelope bound on `Y` | after `Y%12=4` | exact modular minimum |
|---:|---:|---:|---:|
| 1 | 4 | 4 | 4 |
| 3 | 49 | 52 | 220 |
| 5 | 508 | 508 | 508 |
| 7 | 5,956 | 5,956 | 45,052 |
| 9 | 74,896 | 74,896 | 327,676 |
| 11 | 986,893 | 986,896 | 16,252,924 |
| 13 | 13,421,770 | 13,421,776 | 67,108,852 |

## Reproducible exact minimization

The following Python 3 code uses power-of-two residues and arbitrary-precision integers. The logarithmic cutoff limits it to at most floor(log2(6*m))+1 candidates; it returns the exact modular minimum and an attaining exponent residue.

```python
def lower_bound(m: int) -> tuple[int, int]:
    assert m >= 1 and m % 2 == 1
    L = m + 1
    Q = (2 ** (2 * L) - 1) // 3
    candidates = []
    t = 0
    while 2 ** t <= 6 * m:
        modulus = 2 ** (t + 2)
        n = (2 ** (t + 1) - 3 * m) % modulus
        numerator = n * Q - m
        assert numerator % (2 ** t) == 0
        v = numerator // (2 ** t)
        assert v % 4 == 2
        candidates.append((3 * v - 2, t))
        t += 1
    return min(candidates)

for m in (1, 3, 5, 7, 9, 11, 13):
    print(m, lower_bound(m))
```

Exact arbitrary-precision output:

| odd m | exact modular minimum Y | exponent residue d mod (2m+2) |
| ---: | ---: | ---: |
| 1 | 4 | 1 |
| 3 | 220 | 3 |
| 5 | 508 | 3 |
| 7 | 45052 | 4 |
| 9 | 327676 | 4 |
| 11 | 16252924 | 5 |
| 13 | 67108852 | 2 |

For m=1, the genuine source-certified tower [SecondOneInfinite.lean](SecondOneInfinite.lean) has d=4r+5 and terminal Y=4; d≡1(mod4), matching the exact minimization. For m=3,5,7 the displayed minimum also appears among actual (though **not necessarily blank-reachable**) stopping inputs in exploratory exact source-normalization computations. Those observations do not replace the universal modular proof.

## Relevance and limitations

This refines the independent paper proof [DeepResidualExponentialBarrier.md](DeepResidualExponentialBarrier.md), which gives a simple uniform analytic bound `Y≥2^(m+2)-6m-1`. The new finite minimizer often gives much stronger per-m restrictions and can be evaluated without enumerating huge j or k. It specializes to the source-certified deep affine stopping-sector terminal property `Y%12=4` in [DeepSecondFinal.lean](DeepSecondFinal.lean), whose original-source proofs were checked by [CI 42196589496](https://github.com/FlareZ123/bb6/actions/runs/42196589496).

The global Machine C halting/blank reachability question remains open, and no claim here determines BB(6). Strong next work: formalize (★) in Lean against exact original sources and combine the finite set of surviving residue representatives with source-exact backward reachability certificates.
