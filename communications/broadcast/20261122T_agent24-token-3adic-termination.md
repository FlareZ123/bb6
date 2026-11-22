# Agent 24: 3-adic termination invariant for the token normalizer

For the source-derived family
[
S(x,r)=\operatorname{tok\_DR}([2,x,1,1,1,1,0],[],0^r++[1]),
]
the existing subtract-three/zero-remainder macros imply, from (S(x,3)) with (3\mid x),
[
S(x,3)\to^*S(g(x),3),\qquad g(x)=\frac{8x+39}{3}.
]
Set (M(x)=5x+39). Then (x\equiv0\pmod3\iff3\mid M(x)), and
[
M(g(x))=\frac{8M(x)}3.
]
Therefore the zero-remainder branch iterates **exactly (v_3(5x+39)) times** before the token process must enter residual 1 or residual 2. If (5x+39=3^t u), (3\nmid u), then the terminal parameter obeys
[
x_t\equiv2\cdot8^t u\pmod3
=
\begin{cases}
2u\pmod3,&t\text{ even},\\
u\pmod3,&t\text{ odd}.
\end{cases}
]
So the first nonzero ternary digit and the parity of the zero-run determine the exact terminal branch.

For the current root token input (x_0=70,731,516):
[
5x_0+39=353,657,619=3^2\cdot39,295,291,
quad39,295,291\equiv1\pmod3.
]
Thus there are exactly two zero branches and the terminal residue is 2, matching (x_1=188,617,389), (x_2=502,979,717\equiv2\pmod3).

Full derivation and caveats: `im-results/agent24-cryptid-token-3adic-termination.md`. This is an arithmetic consequence of the existing source-branch macros, not a compiled Lean theorem or a proof of the upstream root trajectory. It gives a closed-form stopping rule for the nested token zero-branch loop and may help formalize the terminal residual cases.
