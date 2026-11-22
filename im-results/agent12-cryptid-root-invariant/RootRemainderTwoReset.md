# Remainder-two reset candidate (token-normalizer dependent)

**Status: exploratory finite replay only; not a source-validated theorem.** This candidate extends the source-branch countdown/reset chain, but unlike the zero-remainder reset it uses a DR token-normalizer closure. Its token port must be checked against the pinned #85 proofs before any root-path claim is made.

With (D_n(c)=CR([0],0^{4n+5}++[c])), the corrected exploratory simulator suggests

[
D_n(2)\longrightarrow^{8n+44}D_0(8n+19).
]

The formula was reproduced for (0\le n\le20) by the corrected-CR array replay. For (n=65), it predicts (D_{65}(2)\to D_0(539)) in 564 outer successors. The corresponding exploratory root replay has a DR token closure at global macro 21,810, i.e. 275 outer successors after the proven-chain checkpoint D65(2) at macro 21,535.

## Candidate continuation

If the remainder-two reset is proved, the countdown recurrence and this reset give:

[
D_0(539)\to D_{179}(2)\to D_0(1451)
\to D_{483}(2)\to D_0(3883)\to D_{1294}(1).
]

The last state has remainder one and is the next unresolved case. No claim is made that the candidate reset or this continuation is source-valid.

## Required proof work

1. Identify the exact outer successor at which the DR token closure occurs for general (n).
2. Replace the JavaScript bounce/normalization replay with the pinned source theorem `tok_DR_2_0_closed` (and any required `tok_CR_1_0_closed`) inside a Lean composition.
3. Prove the fixed prefix and suffix around the token closure and establish the parameterized endpoint (D_0(8n+19)).
4. Audit the remainder-one case (D_{1294}(1)); the previous H-phase / 76-step claims are withdrawn and cannot be reused.

The corrected exploratory replay is
[`fast_root_stack_sim_crcorrected_exploratory.js`](./fast_root_stack_sim_crcorrected_exploratory.js).


## More precise token-boundary decomposition (still unproved)

A replay from (D_{65}(2)=CR([0],0^{265}++[2])) locates the token event exactly:
- after 275 ordinary outer successors, the state is
  (DL(0^{267}++[1],[1]));
- the next outer successor is the DL-right-one token closure, with (R_3=[]) and (L=0^{267}++[1]);
- the JS bounce/normalization port returns
  (CR(0^{271}++[1],[0])), i.e. four more zeros are added to the left block.

This suggests the following parameterized decomposition for general (n):

1. (D_n(2)\to DL(0^{4n+7}++[1],[1])) in (4n+15) ordinary successors (8-step prefix, EL-zero sweep of (4n+6), then EL-positive).
2. Apply the pinned source closure `tok_DR_2_0_closed` to the DL-right-one branch:
   (DL(0^{4n+7}++[1],[1])\to CR(0^{4n+11}++[1],[0])).
   This exact endpoint must be checked against the Lean theorem; the displayed endpoint is currently the JS-port prediction.
3. CR-zero sweep of length (4n+11):
   (CR(0^{4n+11}++[1],[0])\to CR([1],[8n+22])).
4. CR-left-one/empty-tail:
   (CR([1],[8n+22])\to EL([0],[0,8n+25])).
5. The same fixed 16-step tail as the zero-reset, generalized from
   (EL([0],[0,x])) to (D_0(x-6)), yields (D_0(8n+19)).

The outer count is
((4n+15)+1+(4n+11)+1+16=8n+44).
For (n=65), this gives (275+1+271+1+16=564), matching the replay. The token event is at global root macro 21,810, after the D65(2) checkpoint at macro 21,535.

This is now a sharply specified Lean target: use the pinned `mode_DL_0_n_closed` / `tok_DR_2_0_closed` proof for phase 2, prove the CR sweep, reuse the CR-one-empty helper, and generalize the fixed tail to (x\ge6). It is still not a proof until the exact token theorem endpoint is checked and the composition compiles.


## External research context: the A-start trajectory is a known probabilistic cryptid

The matching BusyBeaverWiki page identifies this exact machine as an unsolved, "probviously halting" BB(6) cryptid (Racheline, 23 Nov 2024). Its A-start trajectory is the machine encoded by #85. Racheline describes an approximately (8/3) multiplicative update with residue-dependent changes, and gives a length-110 family of 0/2 residue sequences that would force halting if one occurs. The page estimates a halting time around (10^{10^{38.1}}), but this is a probabilistic heuristic, not a proven bound or exact value:
https://wiki.bbchallenge.org/wiki/1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA

The page separately describes an analysis by @-d for a related D-start TNF, with a length-108 residue path and a proved congruence class for that *different* trajectory. Do not conflate it with the A-start problem here. The A-start open question is whether its evolving residue/left-memory process ever enters one of Racheline's halting sequences.

The D_n(c) recurrences derived here are consistent with the advertised (8/3) growth mechanism in the special cases r=0 and r=2. The remainder-one case is exactly where the current simple D-family does not close; this is likely where the left-side memory and the published 0/2 sequence constraints become essential. A useful next target is to derive a complete finite-state or stack-memory recurrence for the A-start process, then prove reachability of a halting residue word rather than relying on the probability heuristic.
