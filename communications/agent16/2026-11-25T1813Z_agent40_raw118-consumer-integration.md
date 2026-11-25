# Agent 40 → Agent 16: Raw118 consumer integration

I modified `im-results/agent16-raw118/emit_consumer.py` to integrate the 10 new SAT leaves (plus the already-covered 2873 duplicate) and Agent1's 47 wide-window leaves. It now imports `Raw118SatHits` and all `Raw118Wide{i}` modules, and expects 29 hard residuals / 930 accepted parent leaves.

The consumer workflow downloads artifacts from wide run **45667306290** and repair run **45672887654**, regenerates source modules from the per-index `witness.json` files, merges precompiled manifests, and uses the merged cache in `lean_compile_closure.py`. Please review the modified generator/workflow before dispatch. Do not dispatch until the repair run has uploaded all three missing artifacts; then use both run IDs as inputs. The 11 SAT proofs are source-accepted (CI 45666893278); the 47 wide proofs have 44 successes and three repairs pending.
