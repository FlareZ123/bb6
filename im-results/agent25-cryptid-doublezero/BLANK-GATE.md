# Agent 25: first unresolved E-on-six-ones section of the genuine blank orbit

**Classification:** conditional symbolic itinerary, intermediate, **not** a global machine decision. All equations below follow mathematically by composing Agent31's full_B/prefix_A/prefix_E rules and Agent25's `close_double_zero`, `e_long`, `iter_triplet`. The individual rules have source-level Lean audits; the cross-encoding composition is not yet an end-to-end Lean theorem. Only the prefix ending at raw step 166,999,736 has also been independently checked by direct simulation.

Write `I_n(r)` for state F scanning a zero, with blank left tape and right tape `1^n r 0^infinity`. For an all-blank suffix, write `I_n`.

The exact conditional section rules are:

- B: `I_(3k+2)(0 ys) → I_(8k+9)(ys)` in `12k²+49k+40` steps (Agent31).
- A: `I_(3k+3)(0 1^(3q) 0 ys) → I_(8k+8q+11)(ys)` in `12k²+49k+44+12q²+(24k+55)q` steps (Agent31 prefix, Agent25 iter_triplet and final sweep).
- E: `I_(3k+4)(0 0 ys) → I_(8k+5)(0 1^6 ys)` in `12k²+49k+50` steps (Agent31 prefix, Agent25 E sweep).

After an E return, if the new unary length is congruent to 2 modulo 3, a subsequent B return consumes the zero and joins the six ones onto the unary run. If it is congruent to 0, the A rule with q=2 consumes the internal block, giving a pure unary section again. The residue 1 modulo 3 requires an **E boundary with six immediate right ones**; these notes do not decide it.

The raw checkpoint checker `check_blank.cpp` verifies `I_27659` at step 166,999,736. The following exact arithmetic then gives the projected first exceptional section:

| Incoming F section | Branch | Outgoing F section | Additional steps | Cumulative raw steps |
|---:|---|---:|---:|---:|
| 27,659 | B | 73,761 | 1,020,331,303 | 1,187,331,039 |
| 73,761 | A, q=0 | 196,699 | 7,254,861,510 | 8,442,192,549 |
| 196,699 | E, 00 | 524,525 with 0 1^6 | 51,588,443,435 | 60,030,635,984 |
| 524,525 with 0 1^6 | B, then join six ones | 1,398,743 | 366,841,070,621 | 426,871,706,605 |
| 1,398,743 | B | 3,729,985 | 2,608,658,026,251 | 3,035,529,732,856 |
| 3,729,985 | E, 00 | 9,946,621 with 0 1^6 | 18,550,405,270,221 | 21,585,935,003,077 |

At that last F section, `9,946,621 ≡ 1 (mod 3)`. The next Agent31 `prefix_E` begins a genuine E boundary with left stack `00(10)^13,262,159 11` and right suffix `1111110...`, at the **projected** absolute raw step `153,499,657,266,461`. This is the first E-on-six-ones question in the above reduced blank trajectory. It has been sent to Agent26, who independently investigates E right-1 branches.

The existing E halting cylinder `1101100` (Agent26) differs from the actual candidate `1111110`; applying that cylinder directly would be unsound. Further work: prove an exact raw E branch on six ones, compose all F-section source definitions in Lean, and evaluate the implications for the blank-tape orbit. A finite-time itinerary does not imply halting or nonhalting forever.
