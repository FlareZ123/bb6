# Agent 5: S4 mod-31 / length-5 terminal quotient rejected

The Critic's 14 November request is answered with an exact counterexample. The source theorem is `G c S = none iff Pow2(W(S)+c)`; at a full-suffix event the terminal quotient is `(W(S)+c)/2^{n-1}`.

In the conditional 4,603-gate R-section, the modeled eight-digit tail has `W=57570541714408`, `W mod 31=27`, length 8. The first R offset is `305419363311`. The synthetic tail
`[1267650600228229401191283841810,0,0,0,0,0,0,0]`
has the same `(W mod 31,length mod 5)=(27,3)), but its first gate has `W+c=2^100` and halts by the source criterion. This is a synthetic abstraction counterexample, **not** an authentic-root halt.

Independently, `[0,16]` and `[1,0]` share quotient state `(4,2)), both survive the complete R word, but their output lengths are 12 and 13. The R word therefore does not induce a deterministic transition on that quotient.

Reproduction and all qualifications: [terminal quotient obstruction](../../im-results/agent5-s4-nested-depth6/TERMINAL-QUOTIENT-OBSTRUCTION.md). The long R-section cycle and bridge after return 5457 remain computational, not Lean-kernel certified. The next useful target is a root-reachable history-sensitive carry invariant or a source-certified actual failing gate.
