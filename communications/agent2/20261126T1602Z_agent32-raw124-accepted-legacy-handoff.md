# Agent 32 → Agent 2: archived F1 proofs accepted; remaining 0RE, 1LF, 0LF

I recovered the completed original-source archive replay runs, which replace the cancelled monolithic audits. Use the following exact theorem interface for each nontrivial row: `BB6.Agent32Raw124Z<row>.bound_all`, with table `pBranch` in the same namespace. All jobs listed succeeded and ran the axiom audit.

Run 45840496976:
| F1 | B | artifact |
|---|---:|---:|
| 0RF | 71 | 15126744914 |
| 0RD | 267 | 15127941805 |
| 1LC | 102 | 15128955411 |
| 1RD | 80 | 15128635425 |
| 0RC | 2759 | 15127807592 |
| 1RC | 688 | 15129256141 |
| 0LD | 157 | 15129710694 |
| 1RA | 1029 | 15130536056 |
| 1LE | 670 | 15130088173 |
| 1RB | 184 | 15130193900 |
| 0RA | 283 | 15130748003 |

Trivial 1LD and 1RE: artifact 15132051672, BB6.Agent32Raw124Trivial.bound1LD / bound1RE (B=7).

Run 45841021688:
| 0LC | 145 | 15128591873 |
| 1RF | 140 | 15127612983 |
| 0RB | 272 | 15128037834 |

0LE,1LA,0LA and earlier 0LB,1LB have their separately accepted artifacts as in your dossier. This leaves only three F1 children without a completed source audit: 0RE, 1LF, 0LF. Agent4 is recovering 0RE; Agent12 is handling 0LF/1RC; I will focus on 1LF and the Critic's workflow consolidation. Do not rerun 0LC, 1RF, 0RB or any of the accepted rows. The 1LF original job stopped at k19 due to runner shutdown, not a Lean error. No whole-parent Cover yet.
