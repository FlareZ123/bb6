# Raw13 coupled six-hole ancestor: two exact delayed queries in E1=1LB

Two previously unresolved one-hole residuals of the E1=1LB sibling (see coupled6-1LB.json) have a common compressed proof. D0 is the sole difference:

| D0 | Table (F0 unassigned) | First F0 query | Halt completion score |
|---|---|---:|---:|
| 0LC | 1RB1LD1RC1RA1LA1RE0LC0LA0RF1LB---0LC | 2,649,126 | 2,649,127 |
| 1LE | 1RB1LD1RC1RA1LA1RE1LE0LA0RF1LB---0LC | 2,651,334 | 2,651,335 |

The first-query count excludes the final halt step; each other row is assigned an ordinary transition. Thus filling F0 with any ordinary transition gives a total nonhalting machine; filling it with halt gives the stated exact score. Both counts were independently reproduced by direct simulation. Unlike increasing the simulation horizon, the proof below supplies arbitrary-parameter sweep identities and a short inductive macro trace.

## Shared exact recurrence

Write X=10, Y=01, U=11. R(w) denotes A with empty left list and right list w, nearest-head first. Let e=0 or 2 respectively for D0=0LC or 1LE. Write V(a,b,w)=R(X^a 0 X^b w). The sweep rule transfers X blocks right-to-left as U, then U left-to-right as Y; each transfer costs 2 steps per block. The D0 variant adds exactly e steps to an odd-length return. The six derived macro rules (input and output at R unless explicitly specified) are:

| Input word | Output word/configuration | Steps |
|---|---|---:|
| X^a 0101 w | X^(a+2) 110 w | 4a+11+e |
| X^a 11 w | X^(a+2) 1 w | 4a+7+e |
| X^a 011 w | 0 X^(a+1) 1 w | 4a+9 |
| X^a 1 | 0 X^(a+1) 11 | 4a+9 |
| X^a | 0 X^a 11 | 4a+5 |
| X^a 01 | F, left 00111 U^a, right empty | 2a+4 |

The first two compose to V(a,b+2,w) -> V(a+5,b,w) in 8a+26+2e steps. Induction yields V(a,2n+b,w) -> V(a+5n,b,w), with cost n(8a+26+2e)+20n(n-1). No bound on a,b,n or the tail w is needed.

The blank orbit has the following exact checkpoints. Between the displayed checkpoints the above rules or the repeated pair rule apply, with n=2,8,20,52,133,333 in that order.

| Configuration | e=0 time | e=2 time |
|---|---:|---:|
| V(0,5,U) | 65 | 69 |
| V(10,1,U) | 157 | 169 |
| V(0,16,U) | 332 | 348 |
| V(40,0,U) | 1660 | 1708 |
| V(0,41,1) | 1829 | 1877 |
| V(100,1,1) | 9949 | 10077 |
| V(0,105,U) | 11200 | 11332 |
| V(260,1,U) | 65592 | 65932 |
| V(0,266,U) | 68767 | 69111 |
| V(665,0,U) | 423345 | 424221 |
| V(0,666,1) | 426014 | 426890 |
| V(1665,0,1) | 2645792 | 2648000 |
| F, left 00111 U^1665, right empty | 2649126 | 2651334 |

In the last configuration F reads zero, the unassigned row.

## Certification and remaining work

[Raw13Coupled6Late1LB.lean](Raw13Coupled6Late1LB.lean) formalizes the exact zipper identities, induction and trace. Lean 4.36.0-rc2 checked the full mathematical trace against a local fixture containing the copied source definitions, reporting only propext and Quot.sound. [Raw13Coupled6Late1LBBound.lean](Raw13Coupled6Late1LBBound.lean) supplies the original-source projection and weighted last-hole checker bridge, with conservative common bound 2,651,340. The focused existing workflow target coupled6Late was dispatched at source commit 13aa4748f8d260fa9bdbf741da3017ec7d34d09e. Full repository import closure and weighted coverage acceptance are pending; the local fixture is not a substitute for that acceptance.

The two other current unresolved E1=1LB leaves are 1RB1LD1RC0RF1LA1RE1LA0LA---1LB0LC0RB and the D1-fixed counterpart with F0=0LD. Their E0 row is unassigned. No full sibling closure is claimed. The prior four extra-BiDFA witnesses remain in coupled6-extra-bidfa.json. After source acceptance, route the two exact late-query certificates directly to bounded leaves instead of the multi-million-step naive chunk trace generator. This increases the sibling bound above 62,123 but remains negligible against the BB6 champion.
