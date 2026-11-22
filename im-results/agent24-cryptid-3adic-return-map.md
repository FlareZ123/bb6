# Exact 9-adic stopping rule for the residual-2 return map

**Status:** proved arithmetic lemma about the conditional stack return map; it is not a proof of the underlying machine trajectory.

The return map in `RootSuffix13Continuation.md` is
[
f(n)=\frac{64n+107}{9},\qquad n\equiv1\pmod 9.
]
It sends the parameter of (D_n(1;[0,0,2])) to the parameter of (E_{f(n)}(13)), conditional on the source-stack macros in that dossier.

## The affine coordinate

Set
[
M(n)=55n+107.
]
The domain condition is exactly
[
n\equiv1\pmod9
\iff 55n+107\equiv0\pmod9
\iff 9\mid M(n).
]
For every (n) in the domain, direct algebra gives
[
egin{aligned}
M(f(n))
&=55\frac{64n+107}{9}+107\\
&=\frac{3520n+6848}{9}\\
&=\frac{64(55n+107)}9
=\frac{64M(n)}9.
end{aligned}
]
Thus the return map is conjugate, in the affine coordinate (M), to division by (9) followed by multiplication by the (9)-adic unit (64).

Since (64\equiv1\pmod9), if (M(n)=9q), then
[
M(f(n))=64q\equiv q\pmod9.
]
Consequently the next return-map application is available exactly when (9\mid q), i.e. exactly when (81\mid M(n)).

## Exact number of consecutive applications

For every integer (n\ge0), (M(n)>0). Let
[
t=v_9(M(n))=\max\{j\ge0:9^j\mid(55n+107)\}.
]
Then the map (f) can be applied **exactly (t) consecutive times** starting from (n).

*Proof.* After (i) applications, induction on (i) gives
[
M(n_i)=\frac{64^iM(n)}{9^i}.
]
The (i)-th application is available iff (9\mid M(n_i)), which, since (64) is coprime to (9), is equivalent to (9^{i+1}\mid M(n)). Hence applications (i=0,\ldots,t-1) are available, while the next one is not. Positivity of (M(n)) makes (t) finite. (square)

This is also the base-(9) digit interpretation. If
[
M(n)=a_0+a_1 9+a_2 9^2+\cdots,
]
then the first (t) digits (a_0,\ldots,a_{t-1}) are zero and (a_t\ne0). The map consumes one such zero digit per application. At the terminal parameter (n_t),
[
n_t\equiv a_t-8\pmod9,
]
because (M(n_t)\equiv a_t\pmod9) and (M(n_t)=55n_t+107\equiv n_t+8\pmod9). Thus the first nonzero base-(9) digit determines the residue class at which this particular return map stops.

## The dossier's concrete parameter

For
[
n_0=22,608,559,198,
qquad M(n_0)=1,243,470,755,997,
]
the least-significant base-(9) digits of (M(n_0)) begin
[
(a_0,a_1,a_2,\ldots)=(0,7,5,8,3,5,7,4,\ldots).
]
Therefore (v_9(M(n_0))=1): exactly one application is possible. It gives
[
n_1=f(n_0)=160,771,976,531\equiv8\pmod9,
]
so the same return map cannot be applied again. This agrees with the next parameter recorded in `RootSuffix13Continuation.md`.

## Consequence for the root proof

The map (n\mapsto(64n+107)/9) is not an indefinitely repeatable invariant. It is a **finite base-(9) zero-run remover**. A proof that uses it repeatedly must also supply the source-derived continuation for the terminal nonzero digit (a_t\in\{1,\ldots,8\}). The present calculation identifies that exact branch selector; it does not determine what the machine does in those other residue classes.

In particular, the example's next class is (n\equiv8\pmod9). The next proof obligation is the authentic source-stack macro for that class (and, for a general theorem, the eight possible terminal digits), not another iteration of the same (f).

This lemma is conditional on the source-stack return map being established. It does not prove that the blank-root trajectory reaches (D_{22,608,559,198}(1;[0,0,2])), does not prove halting or nonhalting of the machine, and does not determine BB(6).
