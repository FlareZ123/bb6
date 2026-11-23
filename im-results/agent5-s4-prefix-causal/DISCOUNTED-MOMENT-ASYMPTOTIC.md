# Discounted moments and the asymptotic positional-moment bound

**Status:** intermediate S4 result in `im-results/`. The nine-digit prefix period and the genuine root state at return 5,457 are source-connected Lean results. The finite constants below are reproduced by exact BigInt arithmetic, not yet kernel-enumerated. This does **not** prove S4 non-halting or determine BB(6).

## Result

For a stack (S=[b_0,ldots,b_{n-1}]), put
[
x_i=b_i+1,qquad
M(S)=sum_i x_i,qquad
D(S)=sum_i i x_i,qquad
P_S(z)=sum_i x_i z^i.
]

The S4 root, conditional on surviving to the relevant gate boundary, satisfies the following all-time discounted-moment bounds. Here (z=2^{-s}).

| (s) | (z) | (alpha_s=\frac32 z^{10}) | Integer (C_s) with (P_S(z)\le\alpha_s M(S)+C_s) | (10-\log_{2^s}(3/2)) |
|---:|---:|---:|---:|---:|
| 1 | (1/2) | (3/2048) | 9,155 | 9.415037499 |
| 2 | (1/4) | (3/2,097,152) | 1,724 | 9.707518750 |
| 3 | (1/8) | (3/2,147,483,648) | 1,036 | 9.805012500 |
| 4 | (1/16) | (3/2^{41}) | 839 | 9.853759375 |
| 5 | (1/32) | (3/2^{51}) | 757 | 9.883007500 |
| 6 | (1/64) | (3/2^{61}) | 720 | 9.902506250 |
| 7 | (1/128) | (3/2^{71}) | 702 | 9.916433928 |
| 8 | (1/256) | (3/2^{81}) | 693 | 9.926879687 |

In particular, if the S4 root survives infinitely, then
[
\boxed{\displaystyle \liminf_{M(S)\to\infty}\frac{D(S)}{M(S)}\ge 10.}
]
This improves the previously used root-history lower-bound coefficient (D\ge 9M+16m) at the asymptotic level. It is a conditional trajectory constraint, not a stopping obstruction by itself.

## Algebraic derivation

Let (G_c(S)=U) be a successful gate. Write (r=v_2(W(S)+c)), and let (t_0,ldots,t_r) be the carry values, with
[
t_0=x_0+c,qquad
t_{i+1}=x_{i+1}+t_i/2quad(i<r),
]
where (t_i) is even for (i<r) and (t_r=m) is odd. Missing input coefficients are zero. The carry identities give
[
(2-z)\sum_{i=0}^r t_i z^i
=2\left(\sum_{i=0}^r x_i z^i+c\right)-m z^{r+1}.
]
Combining this with the weighted-output identity
[
2(P_U(z)-P_S(z))
=2c+(z-1)\sum_{i=0}^r t_i z^i+5z^r-z^{r+1}
]
gives the exact generating-function update
[
\begin{aligned}
P_U(z)={}&\frac{P_S(z)}{2-z}
+\frac{1-z}{2-z}P_{>r}(z)
+\frac{c}{2-z}\\
&+\frac{(1-z)m z^{r+1}}{2(2-z)}
+\frac{(5-z)z^r}{2},
\end{aligned}
]
where (P_{>r}(z)=\sum_{i>r}x_i z^i).

Fix (k=9). At a deep gate, (r\ge k), so
[
P_{>r}(z)\le Mz^{k+1},\qquad m\le M+c
]
for (0<z<1). Therefore
[
P_U(z)\le aP_S(z)+\beta M+\gamma_c c+\delta,
]
where
[
a=\frac1{2-z},\quad
\beta=\frac{3(1-z)}{2(2-z)}z^{k+1},\quad
\gamma_c=a+\frac{1-z}{2(2-z)}z^{k+1},\quad
\delta=\frac{(5-z)z^k}{2}.
]
The mass law is (M(U)=M(S)+c+2). Set
[
\alpha=\frac{\beta}{1-a}=\frac32 z^{k+1}
=\frac32 z^{10},qquad R(S)=P_S(z)-\alpha M(S).
]
The mass-dependent term cancels, leaving the deep-gate inequality
[
R(U)\le aR(S)+\gamma_c c+\delta-\alpha(c+2).
]
At a shallow gate (r<k), the carry is completely determined by the nine-digit prefix, and the exact update is
[
R(U)=R(S)+
c+\frac{z-1}{2}\sum_{i=0}^r t_i z^i
+\frac{5z^r-z^{r+1}}2-\alpha(c+2).
]

The source-certified nine-digit prefix returns to its starting state after 81,920 P-returns. Across this finite cycle, the shallow increments are exact and repeat, while every deep gate contracts (R) by (a<1). There are 703 deep gates in the cycle (245,057 shallow gates). Consequently the period map for (R) is an affine contraction with a finite additive term. It has a finite invariant upper bound (C_s), independent of the growing total mass. Thus
[
P_S(z)\le\frac32 z^{10}M(S)+C_s
]
at every surviving gate boundary.

The reproducible computation uses a (2^{512}) fixed-point scale, exact BigInt shallow updates, and ceiling-rounded deep updates. Its assertions check the prefix period closure, the 703/245,057 gate counts, the return-5,457 mass, and the period-start invariant. See [`discounted_moment_bounds.mjs`](discounted_moment_bounds.mjs).

## Jensen consequence

The weights (x_i/M) form a probability distribution. Since (i\mapsto z^i) is convex,
[
\frac{P_S(z)}{M(S)}
=\sum_i\frac{x_i}{M(S)}z^i
\ge z^{D(S)/M(S)}.
]
Combining this with the all-time upper bound yields
[
\frac{D(S)}{M(S)}
\ge \log_z\left(\frac32z^{10}+\frac{C_s}{M(S)}\right).
]
For each fixed (s), (M(S)\to\infty) along an infinite trajectory, so
[
\liminf\frac{D(S)}{M(S)}
\ge \log_z\left(\frac32z^{10}\right)
=10-\log_{2^s}(3/2).
]
Letting (s\to\infty) gives the claimed lower limit (10).

## Evidence boundary and next use

- The genuine 18-digit state at return 5,457 is certified by `S4PrefixNinthBase.lean` / `S4Prefix5457.seed5457`; the first nine digits are `[283,906,982,3490,3734,5935,13580,109210,171050]`.
- The all-time nine-digit prefix cycle is certified by `S4PrefixNinthCycle.lean`, theorem `root_nine_prefix_mod81920`, in original-source CI [42643801696](https://github.com/FlareZ123/bb6/actions/runs/42643801696). The root bridge is conditional on each prior transition succeeding.
- The source gate and mass identities are in `S4WeightFormula.lean` and the S4 prefix mass modules.
- The 703/245,057 census and the constants (C_s) are exact-integer program results, reproducible by the included script; they have not yet been enumerated inside the Lean kernel.
- The result is not an upper bound on (D), does not eliminate synthetic suffix completions, and does not prove infinite survival.

**Most useful continuation:** combine the (z=1/2,1/4,1/8,ldots) constraints with the existing first- and second-moment tail fibres in `CARRY-MOMENT-NORMAL-FORM.md` and `ROOT-EXTENSION-1310720.md`. The immediate target is a sharper root-reachable interval for the odd quotient at the 703 candidate phases, not another unconstrained prefix-only search.
