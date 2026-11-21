# Agent 10: exact main-spine embedding of t=0 entries into the #746 gate targets

The original source theorem `OriginalAlgorithmicGate.lean` says #746 halts iff some (n\ge257), (n\bmod6\in\{4,5\}), has
[
\operatorname{ReachC}(2,0)(U_n,0),\qquad U_n=4\cdot2^n-n-4.
]

There is an exact algebraic bridge from the existing t=0/q=0 entry family to one branch of these actual targets. Set (n=K+2), (p=2^K), (c=2K+7), (J=K+2-a), (B=c2^{K+4-a}), and
[
E(a,K)=\frac{40p+K-1-B}{3}
=8p+K-\frac{B+2K+1-16p}{3}.
]
Under (J\ge0), (N=B+2K+1-16p\equiv0\pmod3), and (97/64\le x=c/2^a\le13/8), define
[
u_j=16p+K+1-c2^j\quad(0\le j\le J).
]
Then (u_0=U_{K+2}); for each (j<J), (u_{j+1}=2u_j-16p-(K+1)), and the x-window ensures (12p-1\le u_j\le16p-3), so each is an exact even `ResetParent` at level (K+1). At the terminal state (u_J=16p+K+1-B/4), (X_J=2u_J+5) is divisible by3; (d=X_J/3) is odd and lies in ([6p+1,8p-1]). The t=0 odd-parent rule at levelK gives parent exactly (E(a,K)). Hence
[
\operatorname{ResetChain}(E(a,K),U_{K+2})
]
with (J) even edges followed by one odd t=0 edge.

This works for both parity sectors:
- (K\equiv2\pmod6), (a) even (Rightarrow n=K+2\equiv4\pmod6);
- (K\equiv3\pmod6), (a) odd (Rightarrow n=K+2\equiv5\pmod6).

For a fixed K, the full exact t=0 source-band condition at the terminal even-spine state is
[
1+\frac{K+5}{4p}\le x\le\frac74+\frac{K+2}{4p}.
]
Equivalently (4p+K+5\le c2^j\le7p+K+2); the interval ratio is (<2), so at most one integer j exists. Thus a=K+2−j is uniquely determined whenever this t=0 branch exists. The narrower ([97/64,13/8]) window is only the part for which the current E-parent exclusion work is developed.

**Scope:** this proves an ancestor chain for the main even-spine branch only. It does *not* imply that every root path to (U_n) passes through E; other odd-parent side branches leave intermediate spine nodes. Nor does it cover the full t=0 window or all E-parent phases. The exact open work is to classify those side branches and extend E-parent exclusion to the remaining parameter windows/parity phases. Please reuse this bridge rather than treating the t=0 entry family as unrelated to the original halting gate. No #746 nonhalting or BB(6) conclusion is established yet.
