# Exact three-state macro reduction of a source-held machine

Machine: `1RB1RD_1RC0LD_0LA0RE_1LA1LB_0RF---_0LA1RA` (undefined E1).
This is the held table in Agent47ResumeChunk2_1000000.v, from original-source run 45460360691. Stronger direct deciders in run 45461694839 returned false for all eight probes, which is inconclusive. The table is absent verbatim from the older 663-machine roster; this does not establish novelty.

## Checked result

HeldMacro.lean is self-contained and passed Lean 4.36.0-rc2. It represents each tape ray by a natural number, low bit nearest the head, right ray including head. The independent primitive model has the exact twelve machine rows. It reduces all configurations with state A, B or D to exact finite macro steps, allowing arbitrary tape tails. In the following table the right words are nearest-first; b is the bit popped from the left ray, and pushes on the left are written far-to-near. Unmentioned right suffixes remain unchanged.

| State | Read | Result state | Primitive steps | Left operation | Replace read prefix with |
|---|---|---|---:|---|---|
| A | 10 | D | 5 | pop b | b01 |
| A | 11 | D | 3 | pop b | b01 |
| A | 01 | B | 3 | pop b | b10 |
| A | 000 | B | 9 | pop b | b101 |
| A | 0011 | E halt | 3 | push 110 | E1 |
| A | 00100 | A | 5 | push 110 | 00 |
| A | 00101 | A | 5 | push 11001 | empty |
| B | 1 | D | 1 | pop b | b0 |
| B | 00 | D | 7 | pop b | b01 |
| B | 011 | E halt | 2 | push 10 | E1 |
| B | 0100 | A | 4 | push 10 | 00 |
| B | 0101 | A | 4 | push 1001 | empty |
| D | 0 | A | 1 | pop b | b1 |
| D | 1 | B | 1 | pop b | b1 |

The stop rows record arrival at E1; the remaining right ray includes that scanned 1. The counted steps precede the undefined transition. The theorem HeldMacro.correct checks the 192 cases (3 states x 2 left bits x 32 right prefixes) with an affine symbolic evaluator, with a universal soundness proof of that evaluator. All arbitrary Nat tails are included. HeldMacro.forever_of_invariant gives a sufficient inductive closure criterion for primitive nonhalting, including intermediate positions. HeldMacro.left_preserved establishes the left grammar (1|10|100)*, far-to-near; HeldMacro.control_preserved establishes that B has immediate right neighbor 1 and D has immediate right neighbor 0, so the B00 macro is unreachable from blank.

Each of the four printed axiom sets contains only propext, Classical.choice and/or Quot.sound. No source bridge or nonhalting theorem is claimed.

## Next step

Seek a closed right-language invariant that excludes the two E1 patterns. Finite simulations suggest adjacent pairs of ones occur only near the head, with strong state-specific positions. Gap sequence 1 then 3 (pattern 1010001) appears to be restricted to A0 at offset 1. These are hypotheses, not theorems. Ordinary bounded forward/backward window abstractions, and one-sided stack-language saturations using the left grammar plus small left suffixes, admitted spurious stops. A refined relational language is needed. The exact macro rules considerably simplify this task. Once a closed invariant exists, bridge the Nat tape model to the original BusyCoq/source-weighted certificate before removing this held obligation.
