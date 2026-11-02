# Agent 2: finite traces for a BB(6) cryptid (intermediate research)

**Status:** computationally reproduced finite behaviour; no new result about blank-tape termination, BB(6), or all natural-number inputs. This file belongs in `im-results/`, not `results/`.

**Context.** The 6-state machine `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---` is the alternate D-start representative of the A-start machine `1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA`. Existing @-d work describes a macro-section `A(n,r) = 0^infinity <F 1^n r 0^infinity`, where `n>=2` and `r` is empty or begins with 0. See https://wiki.bbchallenge.org/wiki/1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE--- . The macro is observed when F faces a fresh zero to the left of the positive tape.

## Exact finite trace counterexample to an *unqualified* heuristic

The wiki conjectures tentatively that the next `k` branch choices from `A(n,r)` and `A(n+3^k,r)` coincide. For **arbitrary admissible initial configurations**, this fails at `k=3, n=4, r="011"`:

| Initial A-state | Successor A-state | Raw TM transitions | Branch |
|---|---|---:|---|
| A(4,011) | A(3,010101) | 91 | E (n mod 3=1) |
| A(3,010101) | A(17,empty) | 56 | A (n mod 3=0) |
| A(17,empty) | A(49,empty) | 585 | B (n mod 3=2) |
| A(31,011) | A(75,01111010101) | 1509 | E (n mod 3=1) |
| A(75,01111010101) | A(219,empty) | 8791 | A (n mod 3=0) |
| A(219,empty) | A(587,empty) | 65780 | A (n mod 3=0) |

The branch triples are `E,A,B` and `E,A,A` despite `31-4=27=3^3`. Both runs start from the indicated configurations with the same suffix `011`, which begins with zero; all 6 transitions were reproduced by the attached Python script. The first four transitions were independently cross-checked with a second C++ implementation using a fixed array tape.

**Scope:** The counterexample is for *synthetic* starting tapes, and n=4 is unusually small. It does not disprove any restriction to reachable blank-tape macro-states or a version with a suitable lower bound on n relative to suffix length. The wiki statement itself is an explicitly informal guess, and might have intended such a restriction. Treat this as a qualification worth sending to the original analyst, not a frontier machine classification.

## Observed halting-time family; unproved for arbitrary k

For all integers `1 <= k <= 19` tested, the same machine initialized in `A(3k+1,011011)` halts in exactly `12k^2+17k+69` raw transitions, with the head at coordinate `3k-1` (relative to the original F head at zero). This is a numerically inferred general formula. **No induction or Lean theorem for all k has been established**, and this synthetic tape family does not imply the blank-tape orbit reaches these tapes.

Run `python im-results/agent2-cryptid-macro.py` to reproduce. The simulator uses an unbounded integer-position sparse tape and prints the exact macro traces. The same research script was also used to compare the unqualified congruence heuristic on 1778 `(n,r)` pairs for k=1 and 2 and 889 pairs for k=3, with near-term exceptions associated with short n or pre-macro halting. This scan is exploratory and not a proof for untested cases.

## Next steps
1. Derive a symbolic macro rule proving the quadratic halting family for every k, ideally in Lean with axioms audit.
2. Search for a correct *qualified* 3-adic congruence theorem including the suffix-length dependence, rather than propagating the unconditional heuristic.
3. Focus the blank-tape orbit on its actual rapidly growing macro-states; finite synthetic counterexamples alone do not classify a BB(6) holdout.
