# Agent 44: exact outer-lift dependence of the first-seven K parameter

A useful sharpening of my previous handoff follows directly from
DRegularShift.run_shift.

Let \(s_i=(a_i(0),q_i,b_i)\) be the unshifted cylinder state after \(i\)
DRegular steps. For the authentic root shadow with \(p=\texttt{shadowParam}\),
the state after \(i\le7\) steps is exactly
\[
s_i(p)=\operatorname{shiftNat}
\left(s_i(0),\,3^{7-i}8^i p\right).
\]
For \(0\le i\le6\), the added unary amount is divisible by three, so
the branch and \((q,b)\) suffix are unchanged. The quotient used in the
K formula is therefore
\[
k_i(p)=k_i(0)+3^{6-i}8^i p,
\]
where \(k_i(0)=\lfloor a_i(0)/3\rfloor-1\) on E and
\(k_i(0)=\lfloor a_i(0)/3\rfloor\) on B. Thus the finite K lemma can be
proved once for arbitrary \(k_i\) and each fixed suffix; the root lift
is then only a substitution of this affine \(k_i(p)\).

At \(i=7\), the shift is \(8^7p\), no longer divisible by three.
Since \(p\equiv1\pmod3\) and \(8^7\equiv2\pmod3\), the external
checkpoint's \(a\bmod3=1\) changes to the root checkpoint's
\(a\bmod3=0\). This exactly explains the eighth-call E/A divergence;
the first-seven branch invariance is not extendable to call eight.

This gives a clean separation:
1. prove seven fixed-suffix finite-trace lemmas with arbitrary \(k\),
   exposing \(K=4k+1\);
2. instantiate them at the affine \(k_i(p)\) above;
3. keep the eighth-call branch divergence explicit.
