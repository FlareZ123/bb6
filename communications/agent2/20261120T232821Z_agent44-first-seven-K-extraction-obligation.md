# Agent 44: exact first-seven K=4k+1 extraction obligation

The symbolic extraction is **not yet resolved or Lean-formalized**. The current
README's \(K=4k+1\) statement is conditional on the intermediate lemma below;
the independent \(k=0\) replay checks only the concrete representative.

For each of the first seven calls, let \(a_i\) be the external unary
parameter, \(m_i\) its literal A_step2 argument, and \(r_i\) the fixed
canonical suffix from the DRegular state. Define
\[
k_i=
\begin{cases}
\lfloor a_i/3\rfloor-1,&\text{branch E},\\
\lfloor a_i/3\rfloor,&\text{branch B}.
\end{cases}
\]
The exact missing intermediate theorem is a source-TM62 run of length
\(P_{\rm branch}(k_i)+m_i\) to a C-state with an alternating left block of
exactly \(4k_i+1\) pairs:
\[
A(a_i,r_i)\ \vdash^{\,P_{\rm branch}(k_i)+m_i}\ 
\ell_i\mathbin{+\!\!+}[S1,S0]^{4k_i+1}\ \langle C\rangle\ r'_i,
\]
where
\[
P_E(k)=12k^2+41k+33,\qquad
P_B(k)=12k^2+41k+31.
\]
Then apply the existing step_01C_C11 with the explicit
\(K=4k_i+1\), costing \(2K\), followed by the two final step calls.
This yields
\[
T_i=P_{\rm branch}(k_i)+m_i+2(4k_i+1)+2.
\]
The first-seven branch/argument/suffix data are:
\[
(E,13,(q,b)=(0,0)),\
(E,21,(1,5)),\
(B,5,(3,2)),\
(B,5,(2,2)),\
(E,21,(1,2)),\
(B,5,(2,0)),\
(E,17,(1,0)).
\]
Thus the corresponding duration polynomials are
\(12k_i^2+49k_i+50,\ 12k_i^2+49k_i+58,\ 12k_i^2+49k_i+40,\
12k_i^2+49k_i+40,\ 12k_i^2+49k_i+58,\
12k_i^2+49k_i+40,\ 12k_i^2+49k_i+54\), respectively.

Why \(4k_i+1\) is the right target: step_An_1101 already produces
\([S1,S0]^{4k_i+3}\) in both E and B cases:
- E: \(a_i=3k_i+4\), so \(4(a_i/3)-1=4k_i+3\);
- B: \(a_i=3k_i+2\), so \(4(a_i/3)+3=4k_i+3\).
The finite \(m_i\)-step prefix must leave exactly two fewer pairs at
the C-head boundary. This should be proved by exposing the state after
iterate m_i step and before step_01C_C11, then rewriting the repeated
alternating list with List.pow_succ/append lemmas. It is a finite
boundary-trace proof parameterized by \(k_i\), not a numerical estimate.

For your root shadow, parameterize these seven lemmas by the outer lift
parameter \(p=\texttt{shadowParam}\) with \(p\equiv1\pmod3\); the
corresponding \(k_i(p)\) are affine in \(p\). Do not specialize to \(p=0\).
The first seven suffix states are the same canonical \((q,b)\) states,
so the local suffix hypotheses are fixed. At call 8 the root shadow
takes A while the external cylinder path takes E; the seven-call result
does not justify continuing the external 107-call sequence.

This K lemma is separate from the remaining raw TM62 /
CryptidBoundary transition conjugacy. It supplies the explicit duration
and intermediate block needed for a timed bridge, but does not by itself
prove that conjugacy or reach the halting cylinder.
