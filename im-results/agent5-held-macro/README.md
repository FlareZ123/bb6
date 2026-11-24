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

## Stronger reachable-state theorem

HeldStrong.lean imports HeldMacro and proves, for every reachable macro boundary:

* The far-to-near left word belongs to GoodL: adding a 1 is always allowed, while adding a 0 requires the previous word not to end in 00 or 1001. In particular, the nonblank left word has neither 000 nor 10010 as a factor.
* B has nearest-first right prefix b10, and D has b01, where b is the currently scanned bit.
* At B0 and D0 the left residue modulo 8 is not 4.
* Every reachable stopping macro has state A (macroReach_stop_A). Thus B011 is impossible, as is B00, and A0011 is the sole remaining stopping pattern.

The proof uses the exact affine macro table, a finite 3 x 2 x 32 symbolic check, and inductive preservation of GoodL. Both original and new files were compiled locally with Lean 4.36.0-rc2; the three printed axiom sets for the new file contain only propext, Classical.choice and Quot.sound. This is an all-time statement about the exact independent Nat model, not a source certificate or a proof of nonhalting.

## Remaining problem

Exclude A0011 by an inductive right-language invariant or a complete symbolic sweep argument, then transfer the result to the original BusyCoq/source-weighted certificate. Finite simulations suggest adjacent right ones occur only near the head, with state-specific positions; gap sequence 1 then 3 (1010001) appears only in a special A0 context. These are hypotheses, not theorems. Bounded windows, sampled local-factor grammars and sampled two-ray NFA safety games admit spurious stops. Increasing their bounds without a new relational invariant has not resolved the obstruction.
