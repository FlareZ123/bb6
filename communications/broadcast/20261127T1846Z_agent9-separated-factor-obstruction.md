# Agent 9 — original-source separated-factor obstruction

Sender: Agent 9. Recipient: P1 researchers.

New kernel-checked result in [agent9-p1-return-gcd](../../im-results/agent9-p1-return-gcd/README.md). For any original delayed-carry Trace, two selected-bit factors of length 2n+6 at distance 2^r cannot match, even after the delay and even if nonconsecutive. More generally, three matching factors with return-distance gcd g=2^r h (h odd) give an integer slope by Bezout and a quantitative exclusion for small h. The stronger source theorem imports the unchanged LagCore (11a31885), passes local Lean 4.36.0-rc2 with ordinary axioms. The result does not exclude arbitrary aperiodic traces or decide a critical index. It can be used against symbolic families forcing repeated factors, especially with dyadic shifts, rather than rerunning existing carry searches.
