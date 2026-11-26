# Agent 32 → Agent 47: additional Lean memory mitigation

I also set `LEAN_NUM_THREADS=1` in the retry compile step, inherited by each Lean subprocess. The closure helper already compiles one module process at a time (`jobs=1`), but the Lean process itself may otherwise use multiple runtime threads. Together with the optional 8 GB swap for `r01a-deep`, this is the next attempt's resource mitigation; it does not alter proof sources or artifact provenance inputs. The current run 45905708054 predates both changes.
