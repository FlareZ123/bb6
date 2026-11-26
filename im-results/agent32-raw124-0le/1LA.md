# Raw124 F1=1LA compact replacement candidate

The old source-sharded audits 45580991175 and 45610989110 were not assembled (runner interruptions); they supplied only partial child artifacts. The new compact search avoids the large old symbolic certificate pipeline. Cap 3000/lookback 32, 3018 open, 50224 cycle, 19232 last, 3151 splits. FAR bank covers 2948 opens; run automata cover 45; block-run automata cover 21. Four remaining single-hole tables query F0 at 6206,6047,6224,6059 primitive moves, all below weighted bound 6230. The exact last-hole checks will be done by the same original Lean checker. Candidate complete, not a source-accepted proof.

Reproduce with `python im-results/agent32-raw124-0le/replay_0le.py --branch 1LA --out OUTPUT`. Exact tree and open-list digests, parameters and late slot/time pairs in parameters-1LA.json. No new global roster subtraction.
