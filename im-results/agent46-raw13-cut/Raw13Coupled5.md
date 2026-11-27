# Raw13 #1093: five-hole ancestor

Literal p4: `1RB1LD1RC---1LA1RE---0LA---0RD------`. First query D0 at 9 assigned transitions. 25^5 ordinary assignments. D0=1LF has the four-hole graft; five choices 0RA,0RD,1RB,1RC,1RD have side cycles. The other 18 ordinary D0 choices are separately partitioned using existing canonical cut soundness. All eighteen nontrivial sibling bounds are source-accepted. [Raw13Coupled5.lean](Raw13Coupled5.lean) composes them with the five immediate cycles and the four-hole graft; the composite check is pending.

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

The first 101 steps hold for arbitrary tail after the first four Y pairs, producing X^9 1 followed by that tail. The two sweeps have local identities A(0L,XR)→A(0UL,R) and A(UL,R)→A(L,YR) in two steps, with arbitrary L,R; their finite endpoints are the displayed three-/four-step identities or two-step right-edge identities. Thus the return cost is 201+8n, and at n=7k, 201+56k. These strictly positive costs imply unbounded assigned-transition prefixes for every compatible completion, not just a simulation. Lean implementation `Raw13Coupled5Hard0LC.lean` and complete sibling bound passed CI 45949436934.

## Second discovery batch and new periodic witnesses

1LA,1LB,1LC,1LD,1LE,1RA,1RE,1RF supplied 246 literal nonhalting candidates, seven finite late queries (maximum 8864), and five residuals. Longer lag-XOR summaries close three of the five: 1LE holdout lag7, 1RF pair lag10 (645,529,600 states). The other two are 1LC. For B1=1RD, an exact return is F(left=11111,right=Y I^k U), with I=Y^4 and O=11111111. A 28-step pump moves I from right to O on left, with F5 frame on left and Y frame on right. After k pumps, a 10-step endpoint gives F(left=F9 O^k,right=empty); 14-step turn gives A(left=F9 O^k,right=YU). A leftward 8-step pump transfers O to I, repeated k+1 times, leaving A(left=1,right=I^(k+1) YU); a 12-step finish gives F(left=F5,right=Y I^(k+1) U). Seed at 25; return cost 44+36k. This is proved from arbitrary-tail finite identities and inductive sweeps (Raw13Coupled5Hard1LCrd.lean, accepted CI 45949670679). B1=1RE is now closed by the aligned-block invariant below.

## Irregular B1=1RE: global aligned-block summary

Exact table `1RB1LD1RC1RE1LA1RE1LC0LA1RF0RD---0RA`. The alternating tape has irregular marked blocks rather than a simple repeated period. [gramDfa.js](gramDfa.js) summarizes each stack from its outermost nonzero bit: retain length modulo 4, the nearest five bits, and a mask of selected aligned four-bit block types encountered so far. A zero push into the implicit empty stack stays empty. The full six-bit-window symmetric mask closure was 38,971 configurations. Greedy removal of unnecessary mask bits, independently on each side, reduces this to 3,324 configurations and 240 edges (57 and 127 stack summaries). Selected masks 57344 (types 13,14,15) and 40960 (types 13,15). The exact witness is in [coupled5-extra-bidfa.json](coupled5-extra-bidfa.json), the original larger witness in coupled5-1LC-re-original.json. The generator independently reconstructs closure and emits existing rowwise Lean checks. This is a finite inductive invariant, not a simulation horizon argument.

## Accepted sibling proof inventory

| D0 choices | Weighted bound | Source CI |
|---|---:|---:|
| 0LB,0LD | 1007 | 45948470562 |
| 0LC | 1007 | 45949436934 |
| 0LA,0LE,0LF,0RB | 1007 | 45949451049 |
| 0RC,0RE,0RF,1LD | 1007 | 45949456233 |
| 1LA,1LB,1RF | 10007 | 45949461077 |
| 1LE | 1007 | 45949461077 |
| 1RA,1RE | 1007 | 45949466160 |
| 1LC | 10007 | 45950004102 |

All jobs passed full parent bounds and empty complements. These 18 disjoint literal four-hole families represent 7,031,250 completions. The five side-cycle choices cover another 1,953,125; D0=1LF covers 390,625; D0=halt covers the final 390,625. The prospective full 9,765,625-completion theorem at exact weighted threshold 62,123 awaits the small composition check. The original external premise has already been independently source-verified for the nested published machine. None of these subparents alone removes the containing six-hole #1093 from the global retained roster.
