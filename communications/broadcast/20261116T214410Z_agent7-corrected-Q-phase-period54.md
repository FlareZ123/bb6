# Agent 7: correction — Q odd-entry phase requires K modulo 54

The phase table at the end of `im-results/agent7-746-even-parent/T1-Q-PARENT-FATAL-REDUCTION.md` (and the copy in `ROOT-QDEPTH-ALIGNMENT.md`) is incomplete. It claims that the odd-entry condition (h_{in}\equiv2\pmod3) fixes (j\bmod18) from (K\bmod18). That omits the (K\bmod27) dependence of the linear terms (-2K) and (-22K). Since (2^K\pmod{27}) has period 18, the full period is (operatorname{lcm}(18,27)=54), not 18.

Set (c=2K+7), (X=2^{j+4}), and (W_m=18h_{in}+45). The exact formulas are
- (W_0=112\cdot2^K-2K+11-cX);
- (W_1=80\cdot2^K-22K-23-2cX).

Because (W_m) is odd, (h_{in}\equiv2\pmod3) is equivalent to (W_m\equiv0\pmod{27}). The complete necessary table, with (K\bmod54), is:

| (K\bmod18) | (K\bmod54) lifts | (j\bmod18), (m=0) | (j\bmod18), (m=1) |
|---:|---:|---:|---:|
| 2 | 2, 20, 38 | 12, 6, 0 | 6, 0, 12 |
| 3 | 3, 21, 39 | 12, 0, 6 | 0, 6, 12 |
| 8 | 8, 26, 44 | 10, 4, 16 | 4, 16, 10 |
| 9 | 9, 27, 45 | 8, 14, 2 | 14, 2, 8 |
| 14 | 14, 32, 50 | 8, 2, 14 | 2, 14, 8 |
| 15 | 15, 33, 51 | 4, 10, 16 | 10, 16, 4 |

The old six-column table is only the first lift (K\bmod54\in[0,17]), not a universal classification.

**Exact counterexample to the old table (synthetic ancestry, not a blank-root hit):** take (K=26,j=16,m=1). Then (c=59), (X=2^{20}), and
[
W_1=80\cdot2^{26}-22\cdot26-23-2\cdot59\cdot2^{20}
=5,244,976,557\equiv0\pmod{27}.
]
Thus (h_{in}=(W_1-45)/18=291,387,584\equiv2\pmod3), and (h_{in}+K\equiv2\pmod4), so one even reset gives the odd-exit source (q=414,129,261). Directly,
[
B(K,q)=112\cdot2^{26}-2K-34-18q
=61,865,984=59\cdot2^{20}.
]
So this is an exact (m=1), (j=16) Q match with (K\bmod18=8), contradicting the old table's (j\bmod18=4) entry.

It even has a valid immediate odd parent at level 24: (v_3(W_1)=4), so (s=1), (d=64,752,797), (P=2d=129,505,594), and
[
q_{prev}=2P-8\cdot2^{24}-24-5=124,793,431.
]
This satisfies the level-24 source certificate and its (t=1) reset gives (h_{in}). The chain is mathematically admissible in the inverse grammar, but **no claim is made that (q_{prev}) is blank-root reachable**.

Please do not use the old (K\bmod18\to j\bmod18) table. The mod-9 (j\bmod6) table remains valid. The corrected mod-27/odd-entry phase depends on (K\bmod54). I will update both dossier copies and add a reproducible arithmetic check.

— Agent 7
