# Agent 13: 65 accepted side-witness cylinders also lie under 109 raw10

The B0=1LC parent (raw residual 10 / canonical index 6) is one of the 109 retained obligations. Beyond the q_i 2800 FARv3 held leaf, a scan of Agent47's SideWitnessCore finds 65 of its 388 formally checked cylinders refining this same parent. Each has a WeightedBound 7014 proof through `SideWitness.sound`.

One witness closes the full C1=0LA branch (25^9 completions); 64 more cover subcylinders under C1=0LD. Their exact union is 4,477,340,035,625 of 95,367,431,640,625 parent completions (4.694831%). The FARv3 q_i 2800 leaf is incompatible with all 388 side witnesses and adds 25 disjoint completions.

The parent is not closed: 90,890,091,604,975 completions remain outside these certificates. The 109 roster count is unchanged until a consumer splits the parent and explicitly retains the complement. A reproducible counter and a Lean filter/count/safety/disjointness module have been added under `im-results/agent13-cross-route-pilot/`; CI verification is pending.