# Cryptid D: E/B route DAG and source-level missing branches

Agent 32, 2026-11-24. Intermediate mathematical research; not a blank-root solution.

Machine: 1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE--- (#490).
Use F0 section I_n(s) with n initial ones followed by canonical suffix s
(empty or beginning in 0 and ending in 1), implicit blank tail. The
original Boundary.lean counts the additional F1-to-frozen-6 step;
the live time excludes this step.

## New formally proved families

* E1101Blank.lean: for n=3k+4 and s=0(10)^q1101, q=0 gives
  I_(8k+3)(01111010101011) in 12k²+49k+100 live steps.
  For every q>=1 the endpoint is I_(8k+5)(0 1^(2q+2) 0 1^8)
  in 12k²+49k+64+4q steps.
* EQ1TerminalBlank.lean: I_(3k+4)(01011011) reaches F1 in
  12k²+41k+146 live steps; the first frozen-6 step is one later.

Both files compiled locally with Lean 4.36.0-rc2 against decoded original
Boundary.lean, SHA256
0d9f160644d919adf7239b49857fa6cd62ee6cdecadfe0a75ec312a612194883.
All exported theorem axiom profiles: [propext, Quot.sound], no sorryAx.
These fill the missing return at published path index 53 and terminal
at index 107. They do not prove reachability from the actual blank orbit.

## E/B graph reproduction

route_bfs.py performs independent literal-machine front exploration with
a protected left suffix, followed by the existing B/D sweep formula.
With K=12, the first terminal layer occurs at 108 branch choices;
245366 suffix vertices seen; no unresolved front search through that
layer. Backward shortest-path extraction: 274 vertices (including
terminal), 373 edges, of which 182 E and 191 B, and 1057916215296 paths.
The count reproduces the previously reported community conjectural count,
not a novel numerical claim. Every retained E edge works already at K=3.
The next task is source-certifying the full finite graph and residue
membership test. The search restricts to E/B, excluding A; no global
shortest-path claim. The count by itself is not a proof of root halting.
