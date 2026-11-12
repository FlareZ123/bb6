# Four shallow P1 inverse transitions: a quintic energy barrier

**Status.** This note proves an all-index obstruction in the exact scalar
energy model induced by the already source-certified P1 inverse identities.
It excludes four shallow transitions for every critical index n>=76, with
arbitrary depth-two run lengths. The arithmetic proof is complete below.
The composition into a single Lean theorem over `SourceLowWord` has not yet
been compiled; no new original-source CI claim is made here.

## Scalar source interface

Let n>=76, P=2^n, q=8^s, and suppose

```
3*s <= n,       q*p = P,       q*d = 14*n+92.
```

The root energy after the initial depth-two run is 98*p-d. For each of the
four genuine shallow transitions choose t_i in {0,1} and its exact
source-certified profile

```
t_i=0: (alpha_i,C_i,L_i,O_i) = (1,588,84,232)
t_i=1: (alpha_i,C_i,L_i,O_i) = (2,392,56,136).
```

Let u_1,u_2,u_3 be the depth-two run lengths between consecutive shallow
transitions, and let r be the final depth-two run length. Put

```
tau_1 = alpha_1+3*u_1       tau_2 = alpha_2+3*u_2
tau_3 = alpha_3+3*u_3       tau_4 = alpha_4+3*r
A_i = 2^tau_i
T_1 = n+6+3*s
T_2 = T_1+tau_1
T_3 = T_2+tau_2
T_4 = T_3+tau_3
T_5 = T_4+tau_4
R_1 = L_1*T_1-O_1-d
R_i = L_i*T_i-O_i             (i=2,3,4)
E = 112*T_5-384
K+98 = C_1*q + C_2*q*A_1 + C_3*q*A_1*A_2
                 + C_4*q*A_1*A_2*A_3.
```

The exact scalar terminal-wall equation is

```
K*p = A_1*(A_2*(A_3*(A_4*E+R_4)+R_3)+R_2)+R_1.       (1)
```

Equation (1) is obtained by eliminating the five depth-two-run energies
from the four shallow cocycles. The final wall has energy -E. All
coefficients above are the two original-source profiles, not fitted
parameters.

## Theorem

Under these hypotheses, equation (1) has no solution.

## Proof

Write X=n+2 and e=n-3*s. Since q=8^s=2^(3*s), q*2^e=P. Also q divides
14*n+92 and d>=1, so

```
q <= 14*n+92 <= 15*X.                                  (2)
```

The source profiles give 392<=C_i<=588, 56<=L_i<=84 and
0<=O_i<=232. From q*d=14*n+92 and q>=1, d<=14*n+92.

First, T_1<=2*n+6. Therefore

```
R_1 >= 56*(n+6)-232-(14*n+92) = 42*n+12 > 0,
R_1 <= 84*(2*n+6) <= 400*X.                            (3)
```

For i=2,3,4, whenever tau_1+...+tau_(i-1)<=e, we have
T_i<=n+6+3*s+e=2*n+6. Consequently

```
0 < R_i <= 84*(2*n+6) <= 600*X.                        (4)
```

If tau_1+tau_2+tau_3+tau_4<=e, then T_5<=2*n+6 and

```
0 < E <= 112*(2*n+6)-384 <= 2000*X.                    (5)
```

We use the elementary dyadic peeling lemma:

> If K*2^h = A*2^t+R and 0<R<2^h, then t<=h and there is d'>=1
> with R=2^t*d', K*2^(h-t)=A+d', and 2^t<=R.

Indeed, if t>h then 2^h divides R, impossible for 0<R<2^h.
Thus t<=h, and subtracting A*2^t from K*2^h shows 2^t divides R.
Writing R=2^t*d' gives the quotient identity; d'>=1 gives 2^t<=R
and d'<=R.

### Four successive peels

The first shallow equation and (1) give

```
K*2^e =
  [A_2*(A_3*(A_4*E+R_4)+R_3)+R_2]*2^tau_1 + R_1.
```

By (2), (3), and the quintic gap below,

```
q*R_1 <= 6000*X^2 < 2^n = q*2^e,
```

so R_1<2^e. Apply the peeling lemma. It yields tau_1<=e,
a positive d_1 with R_1=2^tau_1*d_1, and

```
K*2^(e-tau_1) =
  A_2*(A_3*(A_4*E+R_4)+R_3)+R_2+d_1,
A_1=2^tau_1 <= R_1 <= 400*X,       d_1<=400*X.
```

Now (4) applies to R_2. Put S_2=R_2+d_1; then 0<S_2<=1000*X.
Using (2),

```
q*A_1*S_2 <= 6000000*X^3 < 2^n
           = q*A_1*2^(e-tau_1).
```

A second peel gives tau_2<=e-tau_1, a positive d_2 with
S_2=2^tau_2*d_2, and

```
K*2^(e-tau_1-tau_2) = A_3*(A_4*E+R_4)+R_3+d_2,
A_2=2^tau_2 <= S_2 <= 1000*X,       d_2<=1000*X.
```

Now 0<S_3:=R_3+d_2<=1600*X. The third scaled remainder satisfies

```
q*A_1*A_2*S_3 <= 9600000000*X^4 < 2^n
               = q*A_1*A_2*2^(e-tau_1-tau_2).
```

The third peel gives tau_3<=e-tau_1-tau_2, a positive d_3 with
S_3=2^tau_3*d_3, and

```
K*2^(e-tau_1-tau_2-tau_3) = A_4*E+R_4+d_3,
A_3=2^tau_3 <= S_3 <= 1600*X,       d_3<=1600*X.
```

Finally, 0<S_4:=R_4+d_3<=2200*X. The fourth scaled remainder obeys

```
q*A_1*A_2*A_3*S_4 <= 21120000000000*X^5 < 2^n
                   = q*A_1*A_2*A_3*
                       2^(e-tau_1-tau_2-tau_3).
```

The fourth peel therefore gives tau_4<=e-tau_1-tau_2-tau_3 and
A_4=2^tau_4<=S_4<=2200*X. In particular the premise for (5) now holds,
so E<=2000*X. The third-peel equality gives the upper bound

```
K*2^(e-tau_1-tau_2-tau_3)
  = A_4*E+S_4
  <= S_4*(E+1)
  <= 2200*X*2001*X
  = 4402200*X^2.                                        (6)
```

On the other hand, the definition of K and C_4>=392 imply

```
K >= 392*q*A_1*A_2*A_3.
```

Since q*A_1*A_2*A_3*2^(e-tau_1-tau_2-tau_3)=2^n, this gives

```
K*2^(e-tau_1-tau_2-tau_3) >= 392*2^n.                 (7)
```

Equations (6) and (7) contradict 4402200*X^2<2^n.

### Quintic gap

For every n>=76,

```
21120000000000*(n+2)^5 < 2^n.                           (8)
```

The five base cases n=76,...,80 are exact integer inequalities:

```
n=76:  60977122652160000000000 < 75557863725914323419136
n=77:  64987431146880000000000 < 151115727451828646838272
n=78:  69206016000000000000000 < 302231454903657293676544
n=79:  73640886549120000000000 < 604462909807314587353088
n=80:  78300254883840000000000 < 1208925819614629174706176
```

For n>=76, n+7<=2*(n+2). Thus
(n+7)^5<=32*(n+2)^5 and 2^(n+5)=32*2^n. Each of the five residue
classes modulo 5 propagates its base inequality by five, proving (8).
This also implies 4402200*(n+2)^2<2^n, as used in (6).

This completes the scalar theorem.

## Relation to genuine P1 source words

The source-to-scalar ingredients already exist and are original-source
Lean checked:

- `SourceTwoChain`, `two_chain_mass` and `two_chain_model` in
  [SourceOneShallowLift.lean](SourceOneShallowLift.lean);
- the exact two source shallow profiles in `source_shallow_profile`
  in the same file;
- the root quotient `root_two_prefix_divisor` in
  [RootTwoDivisor.lean](RootTwoDivisor.lean);
- the exact depth-two energy law `run_energy` in
  [TwoRunModel.lean](TwoRunModel.lean).

A `SourceLowWord` with exactly four shallow constructors has five
`SourceTwoChain` segments and four genuine `inverseAt` shallow edges.
Applying those existing source lemmas produces precisely the variables
and equation (1); the theorem above then excludes its shifted-wall
endpoint for n>=76. The remaining work is to encode this composition as
a new Lean theorem and compile it with the original source imports.
Until that happens, do not describe the four-shallow source corollary as
a new CI-verified theorem.

## Remaining scope

This result does not settle n=14,...,75 in the four-shallow language,
five-or-more shallow transitions, any inverse depth>=3, exceptional
inverse exits, P1 blank-root reachability, or BB(6). It is a genuine
all-index arithmetic advance, not a complete P1 or Busy Beaver result.
