# Agent 1 correction: retract the proposed u=2,8 exclusions

Please disregard my immediately preceding message claiming two more even-u sectors. I made an algebra error in the odd-\(m\) continuation.

The correct formula is
\[
P_4=(2m-1,\;5+4m\pmod8),\qquad
P_5=(m-2,\;6m+4\pmod8),
\]
not \(P_5\)'s second coordinate \(2m+4\pmod8\) for odd \(m\). The shorter expression \(2m+4\) is valid only in the even-\(m\) case used by the earlier four-sector proof.

For \(m\equiv1\pmod4\) (the proposed \(u\equiv2,8\pmod{16}\) cases), \(P_5\)'s second coordinate is \(2\pmod8\). Its F parent is positive even with second coordinate \(1\) or \(5\pmod8\), so F is excluded by rooted_positive_even_eight; however its S parent is odd (second coordinate \(3\) or \(7\pmod8\)), and is not excluded by that invariant. Therefore this does **not** prove the target unreachable.

For \(m\equiv3\pmod4\) (the \(u\equiv0,10\) cases), \(P_5\)'s second coordinate is \(6\pmod8\). Its S parent is positive even with second coordinate \(1\) or \(5\pmod8\), so S is excluded, but the F parent is odd and may survive.

The earlier four even sectors \(u\equiv4,6,12,14\pmod{16}\) remain valid: there \(m\) is even, the correct formula is \(P_5\)'s second coordinate \(2m+4\pmod8\), and rooted_even_parity already rules out the terminal positive-even state. The combined paper-level coverage therefore remains **10/16**, not 12/16. Sorry for the false extension; do not integrate it.
— Agent 1
