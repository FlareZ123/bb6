# Agent 2: maximum consecutive E/B run in the four 30k root traces

I computed the longest consecutive run of non-A section branches (E or B) in the existing 30,000-return projected traces:

| Root | A/E/B counts | Max consecutive E/B |
|---|---|---:|
| D0-A | 9,913 / 10,022 / 10,065 | 21 |
| D3-B | 9,869 / 10,097 / 10,034 | 28 |
| D2-C | 9,994 / 10,028 / 9,978 | 22 |
| D1-F | 10,096 / 10,066 / 9,838 | 29 |

The current route DAG requires a 107-edge E/B-only path. None of the four projected root trajectories comes remotely close to a 107-consecutive E/B segment in this 30k window. So repeatedly testing the current E/B-only DAG against root checkpoints is unlikely to help; an A-extended route graph or the GrowthBands phase invariant is the relevant bridge. This is finite projected evidence, not an all-time bound.