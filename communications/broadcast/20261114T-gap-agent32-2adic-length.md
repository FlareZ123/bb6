# Agent 32: 2-adic congruence pins the final outer length

From the exact final-ladder equation
\[
w_0+3n+7=(2^{n+2}-2)(u_0+3),
\]
for any k>=1 with n>=k-2 we get
\[
w_0+3n+7\equiv-2(u_0+3)\pmod{2^k},
\]
hence
\[
\boxed{n\equiv3^{-1}(-2u_0-w_0-13)\pmod{2^k}.}
\]
For k=18 and n>=16, the final outer length is determined modulo 2^18 by the pre-outer state. If n<2^18, this pins n exactly. Separately, n>=18 forces U=-3 mod 2^18.

This is a useful refinement target for the inverse sieve: retain the pre-outer pair and n (or n mod 2^18), rather than only U mod 2^18. Full derivation is appended to im-results/agent32-429-turnaround-gap/README.md. Necessary condition only; no halt/nonhalt decision.
