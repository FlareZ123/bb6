# Selected-gap defect identity and a terminal-suffix bound

**Status:** exact derivation; partial bound only. This does not prove an unrestricted logarithmic no-short-run bound.

## 1. Exact recurrence and prefix expansion

For a no-short selected-gap path, let
[
C_0=n+3,qquad b_0=-1,
]
and let the successive gaps be (g_j\ge 3). Set
[
s_0=0,qquad s_{j+1}=s_j+g_j,qquad G=s_k,
]
for a prefix of (k) gaps. The selected-gap carry recurrence is
[
C_{j+1}=C_j+g_j,qquad
b_{j+1}=\frac{C_j+b_j}{2^{g_j}}.
]
Write
[
S=\sum_{j=0}^{k-1}2^{s_j},qquad
T=\sum_{j=0}^{k-1}s_j2^{s_j}.
]
Iterating the recurrence gives the exact identity
[
2^G b_k=S C_0+T-1. 	ag{1}
]
In particular, every gap word fixes a unique residue class for (C_0\pmod{2^G}), since (S) is odd.

## 2. Defect identity

Define
[
r_j=C_j-7b_j,qquad C_k=C_0+G,
]
and
[
D=\sum_{j=0}^{k-1}(G-s_j)2^{s_j},qquad
\Delta=2^G-7S.
]
Then (1) gives
[
oxed{2^G r_k=\Delta C_k+7(D+1).} 	ag{2}
]
Also,
[
\Delta
=1+\sum_{j=0}^{k-1}2^{s_j}(2^{g_j}-8)>0. 	ag{3}
]
Thus (r_k>0) for every nonempty no-short prefix.

For the normalized form, put
[
\varepsilon=\frac{\Delta}{2^G}
=2^{-G}+\sum_{j=0}^{k-1}
(1-2^{3-g_j})2^{-(G-s_j)}
]
and
[
\beta=\frac{7(D+1)}{2^G}
=7\sum_{j=0}^{k-1}(G-s_j)2^{-(G-s_j)}+7\,2^{-G}.
]
Then
[
r_k=\varepsilon C_k+\beta. 	ag{4}
]

Because (g_j\ge3), the remaining distances (d_j=G-s_j) satisfy (d_j\ge3(k-j)). Since (x/2^x) decreases for (x\ge2),
[
\frac{D}{2^G}
=\sum_j\frac{d_j}{2^{d_j}}
\le 3\sum_{m\ge1}\frac{m}{8^m}
=\frac{24}{49}.
]
Consequently
[
0<\beta\le\frac{24}{7}+\frac{7}{2^G}<4
\qquad(G\ge6). 	ag{5}
]

## 3. A logarithmic bound on the terminal suffix

A prefix that can be extended by another no-short gap must have
[
8\mid C_k+b_k.
]
Since (C_k+b_k=(8C_k-r_k)/7), this is equivalent to (8\mid r_k). By (2), (r_k>0), so (r_k\ge8). Combining (4) and (5) gives
[
\varepsilon C_k>4. 	ag{6}
]

If every gap in the prefix is 3, then (\varepsilon=2^{-G}), and hence
[
2^G< C_k/4.
]
So an all-3 prefix that can be extended has (G<\log_2(C_k/4)).

Otherwise let (i) be the last index with (g_i\ge4), and put (d_i=G-s_i). All gaps after (i) are 3. In the expression for (\varepsilon), the (i)-th term is at most (2^{-d_i}); earlier terms are bounded using (s_i-s_j\ge3(i-j)), and the leading (2^{-G}) term is at most (2^{-d_i}). Therefore
[
\varepsilon
\le 2^{-d_i}+\sum_{m\ge1}2^{-(d_i+3m)}+2^{-d_i}
=\frac{15}{7}2^{-d_i}.
]
Together with (6),
[
\boxed{2^{d_i}<\frac{15}{28}C_k.} 	ag{7}
]
Thus, in every extendable no-short prefix, the suffix beginning at its last gap greater than 3 (including that gap and all following 3-gaps) has total span (O(\log C_k)). The all-3 case has the same logarithmic conclusion.

For a maximal no-short run, apply this to the prefix before its final gap; the final gap itself is also at most (\log_2(8C/7)), since (2^g\mid C+b\le8C/7). This bounds the terminal portion of the maximal run by (O(\log n)).

## 4. What this does not establish

The estimate controls only the terminal suffix after the last gap greater than 3. It does not bound how many gaps greater than 3 can occur, nor the total span of the earlier part of the run. In particular it does not establish the desired (O(\log n)) bound for an arbitrary switching sequence.

The exact congruence for any extendable prefix is
[
\Delta C_k+7(D+1)\equiv0\pmod{2^{G+3}},
]
which may be a useful route for controlling the number and arrangement of gaps greater than 3.

## 5. Concrete recurrence check

For (n=34990), the no-short gap word
[
(4,6,7,3,7,9)
]
has (C_0=34993), total span (G=36), and final state (C_k=35029, b_k=69), hence (r_k=34546). The exact identity (2) gives the same integer on both sides. This is a recurrence sanity check, not a new theorem about the global machine classification.

## 6. Next mathematical target

The unresolved step is to control the number/total weight of gaps (g_j\ge4), not merely the terminal 3-run. Try either:
1. derive a second defect or valuation potential that decreases across every gap switch; or
2. construct a family of valid gap words showing that the total span can exceed every proposed logarithmic bound.

Keep this result in `im-results/`; it is not a publishable solution of the unrestricted lemma.
