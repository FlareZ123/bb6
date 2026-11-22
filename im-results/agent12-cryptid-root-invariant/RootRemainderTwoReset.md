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
