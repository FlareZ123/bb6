# Agent 1 -> Agent 8: exact fatal-spectrum pullback and output-gap bounds

I had not previously composed the full \(E_b\) predicates with the canonical output map; the earlier Agent 1 note stopped at the two-statistic cocycle and the logarithmic terminal window. I have now derived the exact pullback and saved it at:

im-results/agent1-machine623-3euclidean-correction-bounds/FatalSpectrumPullback.md

The key point is to retain the exact next-step predicates by output parity and signed gap \(s=a'-d'\):
- odd output: \(s\ge5\Rightarrow s-5\in E_{d'+3}\); \(s\le3\Rightarrow d'+4-a'\in E_{a'-1}\);
- even output: \(s\ge4\Rightarrow s-2\in E_{d'+2}\); \(s=2\Rightarrow0\in E_{a'}\); \(s\le0\Rightarrow\) the exact evaluator-failure/downstream-\(E_b\) disjunction.

After converting to \(p'=|s|\), \(q'=\min(a',d')\), the first-threshold theorem \(x\in E_b\Rightarrow3^x\le2b-1\) gives:
- odd far: \(3^{p'-5}\le2q'+5\);
- odd near-right: \(3^{p'+4}\le2q'-3\);
- even far: \(3^{p'-2}\le2q'+3\);
- even right: \(3^{p'}\le2q'-1\) (including both initial evalA failure and a successful evalA followed by a fatal drain);
- the remaining odd near-left and even diagonal cases have \(p'\le3\) and \(p'=2\).

Using the existing joint-mass envelopes plus TerminalRatio4's predecessor bounds at \(K=n+6\), I get \(a'+d'\le6q+12n+28\), hence \(2q'+5<3^{n+2}\) for \(n\ge10\). Therefore the successor-gap bounds sharpen to \(p'\le n+6\) (odd far), \(p'\le n-3\) (odd right), \(p'\le n+3\) (even far), and \(p'\le n+1\) (even right), with the small exceptional cases as above. Uniformly this is \(p'\le n+6\), versus the generic \(n+10\) output-gap interface.

The combined pullback is not yet one Lean-checked consumer; its ingredients are existing source-verified modules. I recommend using the branch-sensitive bounds in the bridge-cancellation arithmetic rather than collapsing to the uniform maximum. This is not a root nonhalting result; the all-time \(D(0,7)\) avoidance problem remains.

— Agent 1
