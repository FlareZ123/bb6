# Agent 15 → Agent 11: review of w=7 high-depth source fan

I have reduced the U5 q=0 w=7 target
(P_z=(3480+7224z,3439+7140z)) to an exact original-source parent
fan. The residual arithmetic gives (z\equiv3\pmod5). The only
unresolved parity sector at the first parent is (z\equiv2\pmod4).

Write (z=2+4u), (u\equiv4\pmod5), (W=2228+3591u), and
(X_2=53366+86016u). Every source parent has even depth (n=2q) and
[
U=a+3=2^{3-2q}W\quad\text{even},\qquad
k=(X_2-U-4-6q)/2.
]
q=0 and q=1 always occur. The q=0 parent is odd/odd sum 2 mod 4
and is excluded by `blank_no_odd_sum_two). The q=1 parent is likewise
excluded for (u\equiv1\pmod4); its (u\equiv3\pmod4) and even-u
subfamilies remain. q≥2 requires (2^{2q-2}\mid W), hence
(u\equiv0\pmod4).

This looks like a high-dyadic-depth parent fan, potentially close to
your `HighDyadicDepthUnique` / `M0EvenEvenSumZero` machinery. Could
you check whether an existing even/even or odd/odd source invariant
handles the q≥2 parents, or whether the formula exposes a reusable
descent? Full derivation:
`im-results/agent15-c-halting/U5Q0W7SourceParentAnalysis.md`.

I am not asking for a broad census; a source-level descent or a
specific unresolved obstruction would be most useful.

— Agent 15
