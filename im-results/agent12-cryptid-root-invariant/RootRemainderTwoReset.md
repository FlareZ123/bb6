# Remainder-two reset candidate (token-normalizer dependent)

**Status: source-level phase derivation; dedicated Lean composition pending.** Unlike the zero-remainder reset, this macro uses a DR token-normalizer closure. Its exact input/output can be derived from the pinned #85 token lemmas (`tok_DR_zero`, `tok_DR_1_nil_28`, `tok_EL_1`, `tok_EL_exit_zero`) and `bumpPairHead [] = [(0,0)]`; a specialized Lean theorem composing those lemmas has not yet been written or compiled. Bounded corrected-CR replay for n=0..20 is corroborating evidence, not the proof.

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


## More precise token-boundary decomposition (source-derived endpoint; Lean composition pending)

A replay from (D_{65}(2)=CR([0],0^{265}++[2])) locates the token event exactly:
- after 275 ordinary outer successors, the state is
  (DL(0^{267}++[1],[1]));
- the next outer successor is the DL-right-one token closure, with (R_3=[]) and (L=0^{267}++[1]);
- the pinned source branch sequence yields
  (CR(0^{271}++[1],[0])), i.e. four more zeros are added to the left block.

The source-derived parameterized decomposition for general (n) is:

1. (D_n(2)\to DL(0^{4n+7}++[1],[1])) in (4n+15) ordinary successors (8-step prefix, EL-zero sweep of (4n+6), then EL-positive).
2. Apply the pinned source closure `tok_DR_2_0_closed` to the DL-right-one branch:
   (DL(0^{4n+7}++[1],[1])\to CR(0^{4n+11}++[1],[0])).
   For this input, `bounce_DR` performs `tok_DR_zero` (4n+7) times and `tok_DR_1_nil_28`, producing K_out=1^(4n+8)++[0] and L_out=[0,0,1]. The `bl_step_macro_len` recursion performs `tok_EL_1` (4n+8) times and `tok_EL_exit_zero`; because R3=[] and `bumpPairHead []=[(0,0)]`, the resulting CR endpoint is exactly the displayed state. A dedicated Lean composition of these source lemmas is still pending.
3. CR-zero sweep of length (4n+11):
   (CR(0^{4n+11}++[1],[0])\to CR([1],[8n+22])).
4. CR-left-one/empty-tail:
   (CR([1],[8n+22])\to EL([0],[0,8n+25])).
5. The same fixed 16-step tail as the zero-reset, generalized from
   (EL([0],[0,x])) to (D_0(x-6)), yields (D_0(8n+19)).

The outer count is
((4n+15)+1+(4n+11)+1+16=8n+44).
For (n=65), this gives (275+1+271+1+16=564), matching the replay. The token event is at global root macro 21,810, after the D65(2) checkpoint at macro 21,535.

This is now a sharply specified Lean target: use the pinned `mode_DL_0_n_closed` / `tok_DR_2_0_closed` proof for phase 2, prove the CR sweep, reuse the CR-one-empty helper, and generalize the fixed tail to (x\ge6). The token endpoint is now derived from the pinned source clauses, but the complete reset composition still needs to compile as a dedicated Lean theorem.


## External research context: the A-start trajectory is a known probabilistic cryptid

The matching BusyBeaverWiki page identifies this exact machine as an unsolved, "probviously halting" BB(6) cryptid (Racheline, 23 Nov 2024). Its A-start trajectory is the machine encoded by #85. Racheline describes an approximately (8/3) multiplicative update with residue-dependent changes, and gives a length-110 family of 0/2 residue sequences that would force halting if one occurs. The page estimates a halting time around (10^{10^{38.1}}), but this is a probabilistic heuristic, not a proven bound or exact value:
https://wiki.bbchallenge.org/wiki/1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA

The page separately describes an analysis by @-d for a related D-start TNF, with a length-108 residue path and a proved congruence class for that *different* trajectory. Do not conflate it with the A-start problem here. The A-start open question is whether its evolving residue/left-memory process ever enters one of Racheline's halting sequences.

The D_n(c) recurrences derived here are consistent with the advertised (8/3) growth mechanism in the special cases r=0 and r=2. The remainder-one case is exactly where the current simple D-family does not close; this is likely where the left-side memory and the published 0/2 sequence constraints become essential. A useful next target is to derive a complete finite-state or stack-memory recurrence for the A-start process, then prove reachability of a halting residue word rather than relying on the probability heuristic.


## Raw TM cost from the pinned token clauses

The token closure has an explicit raw-step cost. For (k=4n+7) leading zeros in the token input:

- DL-right-one prelude: 4 steps (`mode_DL_0_n_closed`, #85 lines 994–999);
- (k) applications of `tok_DR_zero`: (4k=16n+28) steps;
- `tok_DR_1_nil_28`: 28 steps;
- (k+1=4n+8) applications of `tok_EL_1`: (2(k+1)=8n+16) steps;
- `tok_EL_exit_zero`: 1 step.

Total token-closure cost: (24n+77).

Adding the ordinary prefix (raw (8n+34)), CR-zero sweep (raw (8n+22)), CR-one/empty-tail (6), and fixed tail (47) gives the candidate full reset cost

[
40n+186.
]

For (n=65), this is 2,786 raw steps. Added to the source-derived root checkpoint D65(2) at raw time 64,018, the predicted D0(539) checkpoint is raw time 66,804. This matches the earlier independent raw-cost bookkeeping value 66,804, although that note labels the endpoint D0(540); the exact endpoint here is D0(539) under the present definition. The endpoint/cost composition still needs a dedicated Lean theorem.


The full raw reset cost derived from the pinned clauses is (40n+186). At n=65 it is 2,786 steps; added to the source-derived D65(2) checkpoint at raw time 64,018, the predicted D0(539) checkpoint is raw time 66,804. This agrees with the earlier independent raw-step bookkeeping total 66,804, although that note labels its endpoint D0(540); under the present D_n definition and the source-derived endpoint it is D0(539).
