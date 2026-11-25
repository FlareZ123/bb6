# Raw58 0RF triple-digit counter (five exact instances)

The five literal open-leaf tables in Raw58RFTripleCases.lean (indices 116, 317, 345, 350, 353 of the A1=0RF roster, SHA256 0dc1b3f13cc19052c5ef09d5ae7bdf473f246a585918e0574eae9be4d8cd0edf) all execute the same countdown on a finite right-hand digit word. The head-inclusive zipper sections are

- D(r) = state D, left 11, right r;
- F(k,b,r) = state F, left b 00 (000)^k 11, right r.

The language of r consists of zero or more digits 11b, followed by either nothing or 11. At D the word must be nonempty. The blank run reaches D(11) after five ordinary transitions. The three-step anchor consumes the leading digit, interpreting terminal 11 as digit 110 with an implicit blank last cell. In F, a zero digit consumes the next digit and accumulates a triple of zeros on the left. A one digit returns to D with the carried digits restored to 111 and the selected digit 110. At the empty end the overflow restores all carried digits and a nonempty suffix of five or six ones. A structural induction on the remaining digit word proves a positive return; induction on the number of returns then gives arbitrarily long live prefixes. This is a proof for all compatible completions, independent of extrapolating the exponentially spaced boundary events.

| Leaf | Carry cost | Stop cost | Overflow cost | Overflow suffix |
|---|---:|---:|---:|---|
| 116 | 7 | 3+3k | 7+3k | 1^5 |
| 317 | 3 | 7+3k | 9+3k | 1^6 |
| 345 | 3 | 7+3k | 7+3k | 1^5 |
| 350 | 3 | 3+3k | 11+3k | 1^5 |
| 353 | 3 | 7+3k | 11+3k | 1^5 |

The core and all five arbitrary-live-prefix theorems were locally kernel-checked against the exact copied Move/PartialMachine/zipper run/sweep definitions with Lean 4.36.0-rc2, reporting only propext and Quot.sound. The repository cases also apply the existing Raw58Live.never_of_live bridge. Original-source import and full parent integration remain pending; this does not close the raw58 parent or reduce the canonical roster.

The remaining 0RF leaves 141 and 512 use different digit encodings; do not identify them with this language. The five leaf proofs are reusable even if generation of the full residual-child audit is interrupted.
