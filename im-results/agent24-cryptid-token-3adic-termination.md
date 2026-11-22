# 3-adic termination invariant for the residual token normalizer

**Status:** elementary all-parameter arithmetic lemma for the source-derived token recurrence; the source-branch recurrence itself remains an uncompiled intermediate derivation in `TokenResidual2Continuation.md`.

## Token recurrence being analyzed

Use the family
[
S(x,r)=\operatorname{tok\_DR}([2,x,1,1,1,1,0],[],0^r++[1]).
]
The source-lemma decomposition in `im-results/agent24-cryptid-root-proof/TokenResidual2Continuation.md` gives:

- For (x\ge3), one subtract-three cycle sends
  [
  S(x,r)\to S(x-3,r+4).
  ]
- After (N=x/3) such cycles when (3\mid x), the zero-remainder branch sends
  [
  S(0,r+4N)\to S(2(r+4N)+7,3).
  ]
  In particular, when the cycle starts at (S(x,3)) and (3\mid x), the new parameter is
  [
  g(x)=8(x/3)+13=\frac{8x+39}{3}.
  ]
- The residual-one and residual-two cases (S(1,r)) and (S(2,r)) leave this (S)-family through the two distinct outer-stack endpoints recorded in that dossier.

Thus repeated zero-remainder branches from (S(x,3)) iterate (g) exactly while the current (x) is divisible by (3).

## Affine 3-adic coordinate

Set
[
M(x)=5x+39.
]
Then
[
x\equiv0\pmod3
\iff M(x)\equiv0\pmod3,
]
since (M(x)\equiv2x\pmod3). For every (x\equiv0\pmod3),
[
egin{aligned}
M(g(x))
&=5\frac{8x+39}{3}+39\\
&=\frac{40x+195+117}{3}\\
&=\frac{8(5x+39)}3
=\frac{8M(x)}3.
end{aligned}
]

Consequently, if (x_{i+1}=g(x_i)) while (3\mid x_i), then
[
M(x_i)=\frac{8^iM(x_0)}{3^i}.
]
Because (8) is a (3)-adic unit, the zero branch is available exactly
[
t=v_3(5x_0+39)
]
consecutive times. For (x_0\ge0), (M(x_0)>0), so (t) is finite. After precisely (t) zero branches, (x_t\not\equiv0\pmod3), and the token process must enter its residual-one or residual-two branch.

More explicitly, write
[
5x_0+39=3^t u,qquad 3\nmid u.
]
Then
[
M(x_t)=8^t u,
qquad
x_t\equiv 2\cdot8^t u\pmod3.
]
Since (8\equiv-1\pmod3),
[
x_t\equiv
\begin{cases}
2u\pmod3,&t\text{ even},\\
u\pmod3,&t\text{ odd}.
\end{cases}
]
This determines whether the terminal token branch is residual 1 or residual 2 from the first nonzero ternary digit of (5x_0+39) and the parity of (t).

## The root token input in the current dossier

The unresolved token input in `TokenResidual2Continuation.md` reduces to (S(x_0,3)) with
[
x_0=70,731,516.
]
Here
[
5x_0+39=353,657,619=3^2\cdot39,295,291,
]
and (39,295,291\equiv1\pmod3). Hence (t=2), and
[
x_2\equiv2\cdot1\equiv2\pmod3.
]
The exact token recurrence therefore has **two** zero-remainder branches followed by the residual-two branch. This recovers the branch pattern in the existing arithmetic table without relying on a finite search over (x_0).

The corresponding parameters are
[
x_1=188,617,389,
qquad
x_2=502,979,717\equiv2\pmod3,
]
as recorded in the token dossier.

## Research consequence

This turns the nested zero-branch part of the token normalizer into a deterministic ternary digit shift with a closed-form stopping count. For any input in the (S(x,3)) family, the number of repeated zero branches is not an unbounded search: it is exactly (v_3(5x+39)), and the terminal residual is explicitly determined.

The remaining work is to formalize the source-lemma recurrence (S(x,r)), the residual-one/residual-two exits, and their outer-stack compositions in the pinned #85 module. This arithmetic lemma alone does not prove the blank-root path reaches the token input, does not prove the whole machine halts or runs forever, and does not determine BB(6).


## Exact raw cost of the complete token reduction

The same decomposition gives a reusable raw-step formula. Let (x_0\ge0), (t=v_3(5x_0+39)), and let
[
x_{i+1}=\frac{8x_i+39}{3}\quad(0\le i<t).
]
For (i<t), put (N_i=x_i/3). At the terminal parameter (x_t\not\equiv0\pmod3), put (N_t=\lfloor x_t/3\rfloor) and (r=x_t-3N_t\in\{1,2\}).

A batch of (N) subtract-three cycles starting with (r=3) costs
[
\sum_{j=0}^{N-1}(6(3+4j)+35)=12N^2+41N
]
raw steps. Each zero-remainder return costs (8(3+4N)+77=32N+101). The terminal residual-one/two branch costs respectively (24N_t+59) or (24N_t+64). Hence the complete reduction from (S(x_0,3)) to its terminal CR state costs
[
\boxed{
\sum_{i=0}^{t-1}(12N_i^2+73N_i+101)
+12N_t^2+65N_t+
\begin{cases}
59,&r=1,\\
64,&r=2.
\end{cases}}
]
This is a finite exact sum, with the number of terms (t=v_3(5x_0+39)) known in advance. It excludes any prefix required to enter (S(x_0,3)) and any later outer-stack continuation.

For (x_0=70,731,516), (t=2), ((N_0,N_1,N_2)=(23,577,172,62,872,463,167,659,905)), and (r=2). The boxed formula gives
[
391,424,097,862,473,182
]
raw steps from (S(x_0,3)) to the residual-two CR state, matching the sum of the three subtract-three batches, two zero-return branches, and final residual-two branch in `TokenResidual2Continuation.md`. Adding its 70,731,575-step entry prefix gives the dossier's (391,424,097,933,204,757) total.
