# q0-138 remaining two-counter machine

Table: `1RB1LC_1RC1RD_0LA1LA_---0RE_0RF1RE_1RA0LC`; its sole hole is D0. This is the only previously open leaf after complete 644825-node computational candidate scan, run 45926582144.

Use head-relative finite zipper lists, left inclusive of scanned symbol and right exclusive, nearest first. At step 2157 state F has left word `000 1^44 0 1^12`, right empty. Let H(n) be F with `000 1^(34+2n) 0 1^12`, J(x,y) be F with `00 111 0 1^(2+2x) 0 1^(32+2y) 0 1111`. All parameters are nonnegative. The seven positive-cost, exact parametric trace fixtures in q0-138-counter-fixtures.json establish:

| Rule | Source | Target | Primitive step count |
|---|---|---|---:|
| H | H n | J (n+7) 4 | 60n + 0m + 1360 |
| J | J (n+5) m | J (n+1) (m+6) | 24n + 0m + 160 |
| J2 | J 0 n | H n | 16n + 0m + 334 |
| J4 | J 1 n | J (n+14) 0 | 60n + 0m + 1772 |
| J6 | J 2 n | J (n+11) 0 | 60n + 0m + 1394 |
| J8 | J 3 n | H (n+5) | 16n + 0m + 502 |
| J10 | J 4 n | J 0 (n+6) | 0n + 0m + 136 |

Every H or J has an outgoing checked return, so the union is a nonhalting invariant. No single linear growth schedule is necessary. Symbolic transfers use an arbitrary repetition count, and the two-variable rule J keeps the exponents independent. The proof is not finite sampling. The candidate Lean module Agent5MultiPump generalizes the accepted Agent46AutoPump soundness argument, while Raw11Q0Counter138 checks concrete local transfers and the closed region. Original-source kernel acceptance pending.

Current 138 candidate weighted bound remains 1502 if this cylinder is accepted and consumed.
