# Raw13 #1093: five-hole ancestor

Literal p4: `1RB1LD1RC---1LA1RE---0LA---0RD------`. First query D0 at 9 assigned transitions. 25^5 ordinary assignments. D0=1LF has the four-hole graft; five choices 0RA,0RD,1RB,1RC,1RD have side cycles. The other 18 ordinary D0 choices are separately partitioned using existing canonical cut soundness. No global coverage claim until the complete complement is checked.

## First 10 sibling banks

Candidate closure 265/266 residuals: 0LB=13/13, 0LD=15/15, 0LA=64/64, 0LC=38/39, 0LE=27/27, 0LF=43/43, 0RB=22/22, 0RC=2/2, 0RE=1/1, 0RF=40/40. Banks are literal tables and DFA witnesses; all must pass independent FastBiDFA Lean checking. The remaining 0LC residual has the following explicit mathematical proof.

## 0LC residual exact affine return

Machine `1RB1LD1RC1RA1LA1RE0LC0LA0RF0RD---1RC`. The missing F0 is never read. Write zipper lists nearest-first, left including scanned bit, and omitted bits blank. Set X=10,Y=01,U=11. At step 60, state F has left 10111, right Y^4 1. For every n≥0, define family F_n=(F,10111,Y^(n+4)1). The following identities give F_n→F_(n+7):

| Cost | State | Left | Right |
|---:|---|---|---|
| 101 | A | empty | X^(n+9) U |
| 2(n+10) | A | U^(n+10)1 | empty |
| 2(n+10) | A | 1 | Y^(n+10) |
| 3 | A | empty | X^(n+11)1 |
| 2(n+12) | A | 0 U^(n+12) | empty |
| 3 | A | U^(n+13) | 1 |
| 2(n+13) | A | empty | Y^(n+13)1 |
| 4 | F | 10111 | Y^(n+11)1 |

The first 101 steps hold for arbitrary tail after the first four Y pairs, producing X^9 1 followed by that tail. The two sweeps have local identities A(0L,XR)→A(0UL,R) and A(UL,R)→A(L,YR) in two steps, with arbitrary L,R; their finite endpoints are the displayed three-/four-step identities or two-step right-edge identities. Thus the return cost is 201+8n, and at n=7k, 201+56k. These strictly positive costs imply unbounded assigned-transition prefixes for every compatible completion, not just a simulation. Lean implementation Raw13Coupled5Hard0LC.lean is pending compilation at this checkpoint.
