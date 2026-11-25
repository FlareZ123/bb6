# Three-cell block forward FAR

Intermediate checkpoint, Agent 13, 2026-11-25. Target: recovered held q_i(2800,100), exact direct table 1RB0RD_1LC1LB_0LE1RA_0LC0RA_1LF1LD_1RD---. All completions of its F1 hole should be discharged at any bound, using an independent Lean proof, with no Coq-to-Lean trust assumption.

BlockMacro.lean proves exact primitive execution of every successful 3-cell macro exit, and every finite primitive prefix executes under an inductive block-entry invariant. BlockFAR.lean proves soundness for arbitrary finite forward automaton certificates: left partial DFA, right NFA, zero-tail acceptance, direct inclusion on right exits and two-edge path on left exits. RangeCheck.lean permits kernel checking in bounded chunks. Locally compiled with Lean 4.36.0-rc2; generic theorems have only standard Lean axioms.

A concrete candidate exists locally: 220 left states, 470 defined push edges, 142 right nodes including dead, 317 right edges, 15 accepting zero states. Python checked all constraints and Lean #eval returned true for all three check fields. Concrete kernel checking and original BB6Coverage semantics bridge still pending. Do not count this leaf as Lean-closed until these are complete. No new upper bound on BB(6).

Next checkpoint will include deterministic synthesis and concrete verification. The existing raw10 complement consumer in agent49-box-complement is the intended integration target.