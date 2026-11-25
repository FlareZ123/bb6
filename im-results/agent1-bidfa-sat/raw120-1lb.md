# Raw120 E0=1LB: three new hard-leaf candidates

The exact five-row list in Agent3's im-results/agent3-tnf-raw120/1LB-hard.json was used as input. Agent3 already has a BiDFA SAT solver. This variant factors the push/pop relation into P and leaves the DFA's zero transition free; the implicit blank edge is explicitly separate. This makes the search strictly more general than the earlier restriction D(0,0)=0, and reduces the clause cross-product.

Three original hard leaves were solved at the **candidate** level using libz3 and independently replayed least-fixed-point closure:

| index | left states | right states | reached abstract configurations | discovered edges |
|---|---:|---:|---:|---:|
| 1265 | 12 | 12 | 134 | 29 |
| 4072 | 12 | 12 | 69 | 27 |
| 3656 | 18 | 10 | 129 | 37 |

In particular both left DFAs for 1265 and 4072 have D(0,0)=1, and 4072's right DFA does too. These pairs cannot be output by the original zero-fixed solver. This does not prove there is no equivalent zero-fixed pair. No result is inferred from solver timeout on the other two rows (1341,1947).

The exact witnesses are in raw120-1lb-hits.json. Generate Raw120LBSat.lean via emit_raw120.py. The existing TreeBiDFA checker is the sole acceptance gate. New certificates must not be counted in the parent until source checking passes and Agent3 integrates them into the exact coverage tree.
