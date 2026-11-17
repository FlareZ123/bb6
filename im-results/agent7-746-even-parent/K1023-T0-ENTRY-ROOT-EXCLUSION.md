# K=1023 t=0 fatal-source entry: exact local root exclusion

**Status:** finite exact exclusion for this one t=0 candidate, using the complete direct-reset parent grammar. It is not a BB(6) bound.

For \(K=1023\), \(c=2K+7=2053\), \(a=\lfloor\log_2c\rfloor=11\), and the explicit fatal-tail formula gives \(r=1013\). The source-band criterion holds, and \(D_0\equiv2\pmod3\), so any incoming odd parent forces \(q\) even. The parity-sharpened bound gives \(q\le a-3=8\). The reproducer enumerates \(q=0,2,4,6,8\), checks the entry and odd-parent bands, and finds only \(q=8\). The entry is
\[
E=8\cdot2^{1023}+1023-2^8D_0,
\]
and its even-parent band is empty. Its only direct parent is the odd source \(h_0\) at level \(1022\).

The exact ResetParent relation in Agent 10's FirstInverseComplete.lean has two exhaustive cases:
- even: \(6\cdot2^k-1\le u\le8\cdot2^k-3\) and \(2u=8\cdot2^k+h+k\);
- odd: \(d\) odd, \(6\cdot2^k+1\le2^td\le8\cdot2^k-1\), \(2u+5=3^{t+1}d\), and \(2(2^td)=8\cdot2^k+h+k+5\).

Starting from \(h_0\), exhaustive inversion gives a single-parent chain of seven edges: odd \((t=1,k=1020)\), five even edges \((k=1020)\), then odd \((t=0,k=1019)\). The final source has no even parent (its unique possible even level fails the even band) and no odd parent (all \(t<v_3(2u+5)\) fail the odd dyadic band). The script recomputes every height and checks every parent equation/band. Thus \(h_0\) has no ancestral path to root \(2\); consequently this entry is not blank-root reachable.

This uses the exact parent grammar, not a bounded-depth search. The source theorem reset_parent_iff is in im-results/agent10-cascade/FirstInverseComplete.lean on branch agent10/t1-q-fatal-source-20261116; confirm its kernel-checked status when integrating this exclusion.