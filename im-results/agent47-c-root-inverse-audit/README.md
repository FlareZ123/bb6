# Machine C: exact thin-gateway inverse fan

**Status:** all-Nat Lean-checked inverse equivalence and quantitative stopping suffixes on the unchanged CLine accelerator; neither blank nonhalting nor a raw BB(6) bound follows. The new [ThinGatewayExact.lean](ThinGatewayExact.lean) closes the entire inverse fan for each individual thin gateway, including the low exceptional entry omitted in the initial Agent13 derivation. It generalizes the old K≥8 two-branch wrapper to all even K, with both necessity and sufficiency.

## Exact recurrence and closed-form reduction

Write R(a,k,c) for BB6CLine.Reach, rooted at (5,0,1). For every even K and C≥4,
```
R(0,K,C) iff
    (K≥2 and C even and R(K+1,(C+K-2)/2,0))
 or (K≥4 and K divisible by 4 and R(0,(K-4)/2,C+K+1))
 or (K=4 and C odd and R(1,(C+3)/2,0)).
```
This is the theorem `zeroA_reach_iff`. The complete predecessor proof works with the chain coordinates K=a+k and C=c-a; the high decrement preserves both, and every other incoming edge is exactly one of the three entry types. The root is not on such a chain. Every admitted entry also drains forward to its specified endpoint, proving sufficiency.

Each recursive inverse step halves K+4 and subtracts three from C+2K. The middle counter strictly decreases. At arbitrary depth d the terminal pair (L,D) therefore satisfies
```
(L+4)*2^d = K+4
D+2*L+3*d = C+2*K.
```
Theorem `origin_reach_iff` proves the resulting finite inverse fan exact for every even K and C≥4. The terminal L is even, D≥4, and the only remaining entry is either the high c=0 entry (L+1,(D+L-2)/2,0), with L≥2 and D even, or the exceptional low entry (1,(D+3)/2,0), with L=4 and D odd. The reverse direction reconstructs the recursive chain without a depth cutoff.

For a thin gateway T_j=(0,2j,4j+10), theorem `thin_reach_iff` specializes this to the **exact per-index** equivalence
```
R(T_j) iff
   exists m,q,k:
     j+2=2^(2*m)*(q+3),
     k+q+3*m+5=4*(j+2),
     R(2*q+3,k,0)
 or exists m,k:
     m≥1,
     j+2=2^(2*m+1),
     k+3*m+4=4*(j+2),
     R(1,k,0).
```
Here the high branch has d=2m; the low branch has d=2m-1. The arithmetic-only theorem `thin_origin_iff` proves both directions of the parameter conversion. In particular the low branch cannot be dropped at K=4: it comes from the genuine (1,k+1,0) -> (2,2,2k+1) source transition.

The fixed-index fan is logarithmic in j+2: there is at most one high candidate per even divisor exponent of j+2 whose quotient is ≥3, plus the possible exceptional low candidate. This paper-level counting observation does not say that any such candidate is blank-reachable. The existing global high/low stopping criteria in other dossiers have stronger residue sieves; this theorem supplies a direct, complete indexed inverse interface to those sieves, rather than a new machine decision. For example, the old residual T_46 has exactly the three high candidates (93,142,0), (21,175,0), (3,181,0), and no low candidate.

## Verification and reproducibility

Lean 4.36.0-rc2 (b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a), local actual compiler:
- unchanged `im-results/agent11-c-line/CLine.lean`, git blob `2f02db1064f5ff610698071268c6ecbfb8dc7b4b`;
- new `ThinGatewayExact.lean`, git blob `78658b0076c081777913a911c72a00ad51336d21`.

Copy both files into one directory and run `lean -o CLine.olean CLine.lean`, then `LEAN_PATH=. lean -o ThinGatewayExact.olean ThinGatewayExact.lean`. Both exited 0. Axiom audit:
- zeroA_reach_iff, origin_reach_iff, thin_reach_iff: [propext, Classical.choice, Quot.sound].
- thin_origin_iff: [propext, Quot.sound].

No sorryAx or native_decide dependency. This exact CLine dependency is unchanged and byte-identical to the repository. The upstream raw Turing-machine bridge is a separate dependency not imported by this local build; see the [CLine source dossier](../agent11-c-line/README.md). No CI workflow was added.

## Exact quantitative stopping suffixes

[ThinGatewayCounted.lean](ThinGatewayCounted.lean) extends the inverse-fan theorem with **exact accelerator-call counts**, and separately the sum of published rule weights. Let Path(n,w,s,t) mean n successful nextC calls from s to t, with weight sum w. The rule weights come from the comments in the pinned [Cryptids source](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC.lean). The raw primitive-count bridge is established in the next section.

For the recursive fan alone (from (0,L,D) to (0,K,C), under the two closed-form fan identities), theorem fan_counted proves
```
n + 2L + 5d = 2K
3w + 51d = F(K) - F(L)
F(x) = 8(x+4)^2 - 39(x+4).
```
The latter is an integer polynomial identity, stated in Lean without subtraction. The single recursive step costs K-1 calls, and its weight has the telescoping potential above. The high c=0 entry costs L calls and weight 2L²+8L+D-7; the exceptional low entry costs 3 calls and weight D+57.

The terminal wing from T_j to the first c=2 state (8j+10,2,2) costs exactly 4j+4 calls and weight 32j²+122j+100. Therefore:
- high stopping family: exact successful call count n=8j-2q-10m+2;
- low stopping family: exact successful call count n=8j-10m+4.

For both families the total weight is entry weight + recursive fan weight + terminal wing weight. The parameters are (L,D,d)=(2q+2,2k-2q,2m) or (4,2k-3,2m-1), respectively, with K=2j. The final c=2 halt call is not included; the raw bridge below proves its three successful transitions, followed by one terminal halting query.

Theorems high_stop_counted and low_stop_counted construct these paths for every admissible parameter, independently of blank reachability. Path.terminal_unique proves uniqueness of the length, weight, and terminal endpoint of any stopping path, without axioms. This gives a quantitative suffix certificate, not a blank-run time or a classification of C.

Lean 4.36.0-rc2 compiled the new module with no warnings or errors, using the above exact dependencies; all four counted theorems report only propext, Classical.choice and Quot.sound. The file blob is 1118c4f7c8d0d281d91eebf872feb131fa33a123. Run `LEAN_PATH=. lean -o ThinGatewayCounted.olean ThinGatewayCounted.lean` after the preceding two modules. An independent primitive simulation of 4,000 small canonical triples also agreed with the published rule weights, but is finite evidence rather than a raw-source count proof.

## Exact primitive-move bridge and Busy Beaver score

[CRawCountBridge.lean](CRawCountBridge.lean) removes the conditional interpretation of the rule weights. It imports unchanged global coverage semantics `im-results/agent8-coverage-contract/Frontier.lean` (blob 115438c4f244b5416a91be4dd7a3f12103d5448d) and the counted/inverse modules above. The literal `cMachine : BB6Coverage.Machine` is the historical holdout #39 table `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`, states A–F numbered 0–5. Physical semantics is `BB6Coverage.run`.

The proof uses a relative infinite-stream zipper (two Nat→Bool streams), four exact arbitrary-length sweeps (C left, B left, B right, E right), and finite local microprograms on arbitrary untouched tails. For every successful nextC edge, zrule_counted proves its exact primitive weight. The c=2 rule makes three ordinary moves and then has no successor; the original blank tape reaches (5,0,1) after exactly 12 ordinary moves. embed_move proves single-move commutation with the actual Int-indexed tape for both directions and every cell.

```lean
theorem raw_haltsAfter_iff (N : Nat) : HaltsAfter cMachine N ↔
    ∃ n w t, Path n w (5,0,1) t ∧ nextC t=none ∧ N=15+w
```
Here w sums successful accelerator-edge weights and N counts ordinary moves. Frontier counts the terminal query as one additional step: **BB score = 16+w**. Both directions hold; reverse uses positivity of weights and absorbing undefined physical states. Theorems high_blank_score and low_blank_score give actual HaltsAfter and Attainable witnesses conditional only on a weighted authentic blank prefix to the stopping parameter. raw_haltsAfter_iff_families combines both into a complete score-specific iff. No numerical score or C classification is claimed.

**Local acceptance:** exact unchanged Frontier, CLine, ThinGatewayExact, ThinGatewayCounted and CRawCountBridge compiled under Lean 4.36.0-rc2. New source blob 1af5a0bf050620ff5e873c1f4745dbff5c622661. raw_haltsAfter_iff and raw_path axioms [propext, Quot.sound]; family witnesses and combined iff additionally Classical.choice. No sorryAx, custom axioms, native_decide. Copy Frontier.lean into the same build directory and run `lean -o Frontier.olean Frontier.lean` then `LEAN_PATH=. lean -o CRawCountBridge.olean CRawCountBridge.lean`. Consumers using the separate MachineCPath.machineC name may prove definitional equality when importing both modules.

## Remaining root obligation

Eliminate all reachable high and low stopping parameters using actual section-root invariants, or prove an authentic reachable member. No finite inverse-fan theorem closes the unbounded set of j. For the current stronger source-connected criteria see [joint criterion](../agent19-c-odd-dyadic/JointCriterionIntegration.md) and [low-ray dossier](../agent13-residual-frontier/LowRayFullFan.md).

## Earlier intermediate evidence (historical)

The original incomplete two-branch inverse argument and the exceptional low branch were discussed in communications/agent13/20261117T1440Z_agent47-inverse-tree-low-branch.md and 20261117T1445Z_agent47-full-predecessor-split.md. The present proof supersedes the unformalized inverse classification in that note, but not the separate M32 quotient exclusion wrapper.

The exact [forward_prefix.js](forward_prefix.js) macro simulation checked the CLine blank orbit through rank 8,000,011, covering all thin indices j≤1,000,000 by rank monotonicity. Every macro applies one ordinary step followed by min(a,c-3) high decrements if a>0,c≥4. No skipped interior state has a=0. Recorded ordinary transitions: 2,285,059,257,097; boundary macros: 4,571,232; high decrements: 2,285,054,685,865; zero-a endpoints: 1,143,020; thin hits: 0; final triple (5,079,022,1,460,493,3); endpoint FNV-1a checksum a11c234b. This is reproducible finite computational evidence, not a kernel-certified prefix or all-time proof. The historical M512 sieve first admitted index above that bound was 1,000,002; later stronger sieves may alter that status.

[M32ThreeClassInverse.md](M32ThreeClassInverse.md) is a separate draft of three modular progressions (j=7+32n, 16+32n, 54+32n). The old wrapper run 44132508910 passed the eight quotient-closure shards but failed the wrapper. The present generic inverse theorem replaces its chain argument; it does not certify those quotient-specific exclusion theorems. Do not claim them as accepted without compiling their own exact dependency closure.
