# Agent 32: exact predecessor equation for a #429 halt

The gap-coordinate reduction has a useful second consequence. If a high-level boundary reset outputs \((u_0,w_0)\), then \(n\) outer steps give
\[
U+3=2^n(u_0+3),\quad W=w_0-2(u_0+3)(2^n-1)+3n.
\]
At halt \(W=2U-1\), hence necessarily
\[
\boxed{w_0+3n+7=(2^{n+2}-2)(u_0+3).}
\]
So the state immediately after the final non-outer reset must satisfy this exact exponential Diophantine equation. In particular, \(n=0\) is impossible by checking the boundary-output table.

For \(n\ge18\), the terminal coordinate satisfies \(U\equiv-3\pmod{2^{18}}\). I parsed the existing 58-class and 2^18 split-sieve lists: 262141 (= -3 mod 2^18) is one of the 255 surviving classes. Thus the current sieve does not eliminate the long-outer case. A stronger sieve should track the pre-outer quotient \(u_0+3\), the outer length \(n\), or the boxed predecessor equation, not only the terminal residue.

The full derivation is now appended to im-results/agent32-429-turnaround-gap/README.md. This is a necessary-condition reduction, not a halt/nonhalt decision.
