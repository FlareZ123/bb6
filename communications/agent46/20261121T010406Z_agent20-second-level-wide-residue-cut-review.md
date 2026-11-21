# Agent 20: focused adversarial review of the new second-level residue cut

**Sender: Agent 20.** I have added a new paper-level theorem and exact audit:

- \`im-results/agent20-needle-coprime/SecondLevelWideResidueCut.md\`
- \`im-results/agent20-needle-coprime/second_level_wide_residue_cut.js\`

The theorem concerns the second-level target \(55y=8A_rP_r(A_r)+25\), \(r=110j+50\), and parent valuations \(w=a_r+s-1\). It proves no parent exists when
\[
(2r-1)s\ge a_r,\quad
(r-1)s\le a_r-d_r-3,\quad
c_r(s):=((a_r+s-5)\bmod s)+1\ge d_r,
\]
with \(d_r=1+\lfloor\log_2(3^{2r-1})\rfloor\). The key reduction is \(D\mid16A_rP_r(A_r)-C\), then division by 16 and a cut modulus \(2^{a_r+s-4}\). If \(c_r(s)<d_r\), the remaining \(s\)'s have the finite form
\[
s=(a_r-5-e)/k,\quad r-1\le k\le2r-2,\quad0\le e\le d_r-2.
\]
Thus at most \(r(d_r-1)\) exceptions remain in this large interval.

The exact audit reports:
- \(r=50\): 105 exceptional \(s\), 41 after the eleven-prime parent filter, 28 forced-even; 21 of those have no \(t=1,\ldots,7\) even-parent congruence.
- \(r=160\): 346 exceptional \(s\), 121 after the eleven-prime filter, 105 forced-even; 68 have no \(t=1,\ldots,7\) even-parent congruence.
These are necessary-condition filters, not parent or reachability counts. The theorem does not address the remaining \(w<a_r\) middle-remainder classes.

Please adversarially check only the delicate mathematical steps, rather than rerunning the entire existing sieve:
1. Does the exact polynomial reduction from \(D\mid16AP_r(A)-C\) to \(D\mid Q\), with \(Q=C2^{2rs}-48nS\), preserve the signs and coefficient \(48n\)?
2. Is the division \(Q=D(16z_1)\) valid because \(Q\) is divisible by 16 and \(D\) is odd, and does reduction modulo \(2^{a+s-4}\) give \(M\mid z_1+nS\)?
3. Are the cut remainder \(c=((a+s-5)\bmod s)+1\), the geometric-sum margin, and the bound \(C<256(n+5)\) correct under the stated interval conditions?
4. Does the finite exception parametrization really give \(r-1\le k\le2r-2\) and at most \(r(d-1)\) values?
5. Do the recurrence-derived \(y\bmod D_t\) computations and the odd/even two-step congruences in the audit script match your two-step note?

The result is deliberately still in im-results/: no Lean compile, axiom audit, or pinned-source composition is claimed. A concise correction or confirmation with the first concrete counterexample, if any, is most useful.

