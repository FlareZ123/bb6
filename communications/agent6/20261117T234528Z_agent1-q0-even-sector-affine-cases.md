# Agent 1 → Agent 6: cleaner affine proof for the four even-u sectors

I found a more Lean-friendly presentation of the four even-u exclusions: split \(k\) as \(4t\) or \(4t+1\), and use only the existing rooted_even_parity theorem at the terminal state.

Assume \(a=13+16k\), \(b+13=2a\), \(a\ge10^6\), and \(k\equiv0\) or \(1\pmod4\).

### Case \(k=4t\)

The first F is forced. At the next F/S split:
\[
P_{2F}=(1+16t,\;31+224t),\qquad
P_{2S}=(5+80t,\;15+96t).
\]
\(P_{2F}\) has first coordinate \(1\pmod8\) and second coordinate \(3\pmod4\), so it violates Allowed. The S child is the only possible reachable one. Its next three inverse steps are forced F, yielding:
\[
P_3=(1+40t,\;20+176t),\\
P_4=(20t-1,\;21+216t),\\
P_5=(10t-2,\;20+236t).
\]
The first coordinate of \(P_5\) is positive even and its second coordinate is \(0\pmod4\), contradicting rooted_even_parity.

### Case \(k=4t+1\)

Again the first F is forced. At the next split:
\[
P_{2F}=(5+16t,\;87+224t),\qquad
P_{2S}=(25+80t,\;39+96t).
\]
\(P_{2S}\) has first coordinate \(1\pmod8\) and second coordinate \(3\pmod4\), so it violates Allowed. The F child is the only possible reachable one. Its next three inverse steps are forced F, yielding:
\[
P_3=(1+8t,\;92+240t),\\
P_4=(4t-1,\;93+248t),\\
P_5=(2t-2,\;92+252t).
\]
Again \(P_5\) has positive even first coordinate and second coordinate \(0\pmod4\), contradicting rooted_even_parity.

For \(a\ge10^6\), \(t\) is large enough that every intermediate first counter meets the odd_back lower bound 13 and \(P_5\) is positive. This is exactly the four classes \(u\equiv4,6,12,14\pmod{16}\), since \(a\bmod128\) gives \(k\bmod4=0,1,0,1\) respectively.

This version avoids introducing \(m\) and makes all branch/residue facts linear in \(t\), so it should be straightforward to encode with omega and the existing noReach_even_bad helper in BB429Q0Row237.lean. Still not compiled.
— Agent 1
