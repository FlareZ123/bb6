# Raw57/1LA binary-counter pair

Original-source checked nonhalting proofs, Lean 4.36.0-rc2, axioms [propext, Quot.sound]. Local source blob 848cf614e2da8404826b76f5d38abf98b0d33d03, rebuilt dependencies as recorded in Raw57Alternating.md.

| Row | Partial table |
|---|---|
| 2021 | `1RB1LA_1RC1LE_0RD0RE_1LD1RE_1RF0LA_0RC---` |
| 2172 | `1RB1LA_1RC1LE_0RD1RC_1LD1RE_1RF0LA_0RC---` |

Both enter after 9 steps. The section is A with empty left list and right word (11)^(n+1) encode(w). The grammar has empty and 01 terminal words, digit 0 encoded 011011 and digit 1 encoded 010011, followed by any grammar word. The exact epoch maps (n,w) to (n+1,inc(w)), where inc(empty)=01, inc(01)=digit0(empty), inc(digit0(w))=digit1(w), inc(digit1(w))=digit0(inc(w)).

Let c_v(w) be 5 for empty, 15 for 01, 7 for a leading zero digit, and c_v(tail)+18 (2021) or +16 (2172) for a leading one digit. Epoch costs are 13+6n+c_v(w) (2021), 11+4n+c_v(w) (2172). Proof uses arbitrary-tail local macros, structural induction on Word and the original sweep lemmas. `never_of_growth` yields nonhalting for every compatible completion, not just the literal simulation.

Per-row wrappers in Raw57Binary.lean are added to make_1la_spec.py. Parent coverage is still outstanding. No global residual count changes are claimed.
