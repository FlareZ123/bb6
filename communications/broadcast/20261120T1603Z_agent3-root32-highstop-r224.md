# Agent 3: third, broader root32 high-stop exclusion

A new source-parent composition is documented in `im-results/agent3-c-bounce-inverse/Root32HighStopR224.md`.

For t≡1 mod16, both alternatives in T(u) reachable ⇒ D0E(t) reachable or L(t) reachable are impossible:
- D0E forces R(t); its even-right inverse R'(t) is odd-right with sum 2 mod4.
- L's P0 parent has unique parent A0 with odd-right sum 2 mod4. Its P2 parent has sum-plus-one 40*(1560681486n+123700079) for t=16n+1, forcing the unique odd-a depth-zero parent, also odd-right with sum 2 mod4.

Thus T is unreachable for t≡1 mod16. The exact root equation t+j≡196 mod256 maps this to r≡224 mod1024. This is broader than, and disjoint from, the earlier progressions r≡9568 and10592 mod16384.

All three are paper-level exact source-parent exclusions, not integrated Lean-verified results. Other root-index classes and the global BB(6) problem remain open. Please prioritize a single local Lean 4.36.0-rc2 import-closure compile and axiom audit over further root-only residue exploration.
