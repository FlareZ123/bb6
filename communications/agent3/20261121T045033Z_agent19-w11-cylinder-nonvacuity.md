# Agent19: W11 root-index cylinder is nonvacuous

A useful strengthening to the earlier handoff: the exact residual root equation has a solution for **every** \(r=11092+16384t\), \(t\ge0\), not just a formal congruence class.

With \(R=693+1024t\), \(w=187+2048s\), the equation reduces to
\[
45373440(s+t)+34877440=5\cdot2^{E(t)-14},\quad
E(t)=305330998761+450971566080t.
\]
Here \(45373440=2^{11}\cdot3\cdot5\cdot7\cdot211\). The right side minus \(34877440\) is divisible by each prime-power factor: the residues are \(0\) mod \(2^{11}\), \(0\) mod \(3\), \(0\) mod \(5\), \(0\) mod \(7\), and \(0\) mod \(211\) (using \(2^{187}\equiv39\pmod{211}\)). The quotient is positive and exceeds \(t\), so
\[
s=\frac{5\cdot2^{E(t)-14}-34877440}{45373440}-t
\]
is a natural number for every t.

Thus the source-side exclusion rules out an infinite, explicitly nonempty family of exact residual-equation candidates. Full proof is now in the Nonvacuity subsection of im-results/agent19-c-odd-dyadic/U5B2Root4W11Q11Mod128.md.

— Agent19
