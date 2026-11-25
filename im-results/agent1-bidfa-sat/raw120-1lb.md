# Raw120 E0=1LB: three source-accepted hard-leaf proofs

The exact five-row list in Agent3's im-results/agent3-tnf-raw120/1LB-hard.json was used as input. Agent3 already has a BiDFA SAT solver. This variant factors the push/pop relation into P and leaves the DFA's zero transition free; the implicit blank edge is explicitly separate. This makes the search strictly more general than the earlier restriction D(0,0)=0, and reduces the clause cross-product.

Three original hard leaves were solved at the candidate level and then source-accepted using libz3 and independently replayed least-fixed-point closure:

| index | left states | right states | reached abstract configurations | discovered edges |
|---|---:|---:|---:|---:|
| 1265 | 12 | 12 | 134 | 29 |
| 4072 | 12 | 12 | 69 | 27 |
| 3656 | 18 | 10 | 129 | 37 |

In particular both left DFAs for 1265 and 4072 have D(0,0)=1, and 4072's right DFA does too. These pairs cannot be output by the original zero-fixed solver. This does not prove there is no equivalent zero-fixed pair. No result is inferred from solver timeout on the other two rows (1341,1947).

The exact witnesses are in raw120-1lb-hits.json. Generate Raw120LBSat.lean via emit_raw120.py. The existing TreeBiDFA checker is the sole acceptance gate. New certificates must not be counted in the parent until source checking passes and Agent3 integrates them into the exact coverage tree.

## Source acceptance

Original-source Lean run [45663147964](https://github.com/FlareZ123/bb6/actions/runs/45663147964) succeeded after opening the required Agent16BiDFA namespace. The named theorems BB6Coverage.Agent1BiDFASat.Raw120LB.M1265.never, M3656.never and M4072.never were audited. These close three of the five previously listed one-hole residuals; integration into the raw120 E0=1LB parent remains Agent3's task. All three are nonhalting for every compatible completion. The original failure 45662679748 was solely a namespace error, corrected by commit 4b8fa25f6640cbd34f64165ccb546164a6308e36.

## Fourth accepted leaf

# Raw120 1LB four of five hard leaves accepted

Run 45665829257 additionally accepted BB6Coverage.Agent1BiDFASat.Raw120LB.M1947.never (width9 sparse ngram compressed to 23x25 stack automata, 679 reachable states and 68 edges). Earlier 1265,3656,4072 accepted in run 45663147964. All exact witnesses in im-results/agent1-bidfa-sat/raw120-1lb-hits.json; emit_raw120.py builds source module. Only 1341 remains from the original five. Please consume these theorems in the exact parent audit. SAT timeouts and failed window/run abstractions on 1341 are not halting evidence.
