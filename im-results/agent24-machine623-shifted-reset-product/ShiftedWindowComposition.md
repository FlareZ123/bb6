# Two-step S-window composition: why suffix offsets 1 and 2 suffice

**Status:** exact index/phase derivation. The source-to-target digit transducer and authentic root hypotheses remain separate obligations.

Let \((k_n,j_n)\) be the S-window indices at root state \(n\), and write
\[
\delta k_n=k_{n+1}-k_n,\qquad
\delta j_n=j_{n+1}-j_n.
\]
The established shift set is
\[
(\delta k_n,\delta j_n)\in\{(0,0),(0,1),(1,1)\}.
\]
Define the source-to-target output stream for transition \(n\) by
\[
S_n=(z_{k_n+1},z_{k_n+2},\ldots,z_{j_{n+1}-3}).
\]
Its low prefix has length \(1+\delta k_n\), and the target window at state \(n+1\) is
\[
W_{n+1}=S_n[1+\delta k_n:].
\]
This is exactly the offset-1 or offset-2 suffix used by the selected-offset automaton.

Now compare consecutive source-to-target streams. The stream \(S_{n+1}\) begins at \(k_{n+1}+1\), which is \(\delta k_n\) symbols after the start of \(S_n\). Its high endpoint is \(j_{n+2}-3\); relative to \(S_n\), this adds a high extension \(h_{n+1}\) of length \(\delta j_{n+1}\in\{0,1\}\). Hence
\[
S_{n+1}=S_n[\delta k_n:]\ \Vert\ h_{n+1}.
\]
The next target window is the suffix of \(S_{n+1}\) after \(1+\delta k_{n+1}\) symbols:
\[
\begin{aligned}
W_{n+2}
&=S_{n+1}[1+\delta k_{n+1}:]\\
&=S_n[1+\delta k_n+\delta k_{n+1}:]\ \Vert\ h_{n+1}.
\end{aligned}
\]

The three-state boundary clock \(r_n=j_n-3k_n\in\{-2,-1,0\}\) has transitions:
- \((0,0)\): \(r\to r\);
- \((0,1)\): \(-2\to-1\) or \(-1\to0\);
- \((1,1)\): \(0\to-2\).

Therefore \(\delta k_n=1\) forces \(r_{n+1}=-2\), and every edge out of \(-2\) has \(\delta k_{n+1}=0\). Thus
\[
\delta k_n+\delta k_{n+1}\le1,
\]
so the suffix offset in the formula for \(W_{n+2}\) is always
\[
1+\delta k_n+\delta k_{n+1}\in\{1,2\}.
\]

This is the precise reason the simultaneous two-copy product needs only offsets 1 and 2:
- offset 1 gives the suffix when both consecutive low shifts are zero;
- offset 2 gives the suffix when exactly one of the two low shifts is one;
- offset 3 is impossible by the boundary-clock constraint;
- offset 0 is never a target window because every target starts after at least one low output pair.

The 3,101-state product in ShiftedResetCarryDFA2.js tracks both offset-1 and offset-2 suffix automata on the same stream. Append the optional high-extension symbol \(h_{n+1}\) to both copies, then select the copy indexed by \(1+\delta k_n+\delta k_{n+1}\). Its carry output and first-reset event symbol decode the exact full post_reset_pair output label by the all-state quotient certificate.

This gives an exact finite recognizer update for the overlapping-window indices, conditional on the source-to-target stream \(S_n\) and high-extension symbol being the authentic ones. It does not by itself prove that the root transition produces those symbols or that the source carry lies in the full start rectangles.

## Finite regression of the root adapter

I tested the exact phase-selection and high-extension logic used by ShiftedWindowInterface.js against the full post_reset_pair DFA. There are 12 valid three-phase paths. For every stream of length 0 through 4, I tested the no-extension case when the second edge has delta_j=0, and all nine possible high-extension symbols when delta_j=1. This gives 450,241 cases; the selected two-copy output, decoded through full_output_lookup, matched the full DFA on the expected suffix in every case. This is a finite regression only; the all-word argument is the suffix/product construction above.
