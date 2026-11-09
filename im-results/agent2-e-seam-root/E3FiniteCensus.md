# Finite-right-suffix census for original D's fixed E3 core

**Agent 2, 9 November 2026. Computational evidence, not a proof.**
Motivation: the verified all-k first-event theorem reduces every prepared E-residue F
section `I_(3k+4)(0Y)` to the fixed nine-left-bit E3 core of `Y`.
It is important to know whether that core can diverge before touching its
protected left marker or entering F/1 on an arbitrary *finite* suffix.

[The C++20 enumerator](E3FiniteCensus.cpp) runs the **literal original
six-state D transition table** on `I_4(0Y)`, which reaches E3 after
the source-certified 33-step delimiter prefix. It scans all 26-bit suffix
lengths in canonical form: the empty suffix and every nonempty word
with a final 1, omitting only duplicates produced by trailing zero padding.
Total: **67,108,864 distinct finite suffixes**, lengths 0 through 26.
The primitive event is the first positive F/0 state with physically blank
left tape, or F/1 halt gate. Each run uses a cap of 200,000 primitive steps.
No run hit the cap or the allocated tape boundary.

| Final-one suffix length | Distinct words | F/0 first return | F/1 first halt | Maximum steps |
|---|---:|---:|---:|---:|
| 15 | 16,384 | 16,118 | 266 | 198 |
| 16 | 32,768 | 32,238 | 530 | 248 |
| 17 | 65,536 | 64,472 | 1,064 | 266 |
| 18 | 131,072 | 128,956 | 2,116 | 280 |
| 19 | 262,144 | 257,901 | 4,243 | 280 |
| 20 | 524,288 | 515,815 | 8,473 | 284 |
| 21 | 1,048,576 | 1,031,626 | 16,950 | 308 |
| 22 | 2,097,152 | 2,063,261 | 33,891 | 326 |
| 23 | 4,194,304 | 4,126,522 | 67,782 | 362 |
| 24 | 8,388,608 | 8,253,040 | 135,568 | 330 |
| 25 | 16,777,216 | 16,506,096 | 271,120 | 376 |
| 26 | 33,554,432 | 33,012,187 | 542,245 | 398 |

The observed maximum across all suffix lengths `n≤26` is 398 steps.
The starting F head reaches at most 6 cells to its left.
The rightmost visited cell is at most 3 cells farther right than an
initial upper bound of 6+n cells past its head. These are
**finite observations only**; no inductive bound is yet established.

## Mathematical conjecture and proof target

The data suggest that, for every finite binary suffix `Y`, the E3
core either first exhausts the left list in the certified C/1 state
or reaches the F/1 halt gate at finite raw time. If established
universally, the no-contact/no-halt divergence branch of the
source-certified all-m E and original F dichotomy could be eliminated
for finite tails.

An especially useful strengthening would be a uniform **linear**
first-event bound in `|Y|`, supported by exhaustive small-prefix
structure. Establishing this requires a parametric source-level scan
or a termination ranking on the uninspected right suffix. Existing
finite-window E marker-safety certificates control the *type* of
left-marker contact but alone do not prove such termination.

The present enumeration is an experimental search that identifies a
promising proof direction, with explicit guardrails against promoting
finite evidence into an unbounded theorem. It has no implication
for halting or nonhalting of the genuine D blank orbit by itself.

## Reproduction and caveats

The program is platform-independent C++20. Arguments give maximum
suffix length (default 26) and primitive-step cap (default 200,000).
The finite tape array and overflow checks are included in the source.
The simulator's left-of-head nonzero counter is updated under the literal
left/right write-move rules; F/0 physical return is recognized only
when it equals zero, and time zero is excluded.

The table reports both categories directly. Termination in all finite
cases tested is a **statement about the tested finite words**, with
no assumption of probabilistic sampling and no mathematical
extrapolation. For a proof, implement symbolic right-tail block
consumption and show a strictly decreasing unread-suffix measure.
