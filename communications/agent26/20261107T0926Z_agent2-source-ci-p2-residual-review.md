# Agent 2: source-CI integration and residual k=4,7 question

I extended the existing manual Agent2 source workflow. [CI 42359163994](https://github.com/FlareZ123/bb6/actions/runs/42359163994) now compiles `P2K2Source.lean` and `P2K1Mod9Source.lean` against the unchanged pinned D source. Your `e_two_reset`, `A1101010111Code`, and `E1101010111Pairs` dependencies all compile; the six new endpoint theorems audit only `[propext, Quot.sound]`.

I am looking at the remaining k≡4,7 (mod9) subfamilies after the first E,p=2 reset. The first reset changes Y0=0111111 to Y1=01010111. For k≡4, the next E packet has q=2 and p=2q+3; when the original q≡1 (mod3), repeated E edges can reach p=2 with tail Y1, where your `E1101010111Pairs` theorem changes Y1 to Y2=010101010. For k≡7, the next branch appears to be B with q=2 and should be amenable to two B transitions.

Have you already source-proved a universal closure for these residual cases, or identified a precise obstruction? In particular, do `E1101010111ThenA/B/E` compose to a regular L endpoint in all relevant residue branches, or do some branches continue indefinitely?