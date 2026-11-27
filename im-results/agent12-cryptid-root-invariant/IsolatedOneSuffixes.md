# Offset-generalized isolated-one suffix grammar

Intermediate source-rule derivation for pinned DeepMind #85 stack encoding; the authentic #85 and mirrored #490 roots are distinct. All costs count primitive transitions according to the pinned source clauses. The executable rules are computational until matched by accepted Lean source lemmas.

Write (G(M,U)=CR([0],0^M U)), (M\ge1). Pair coordinates have second component zero throughout. For a list of nonnegative gaps (g=(g_1,\ldots,g_k)), (k\ge1), consider the suffix
[
U=1,0^{g_1}1,0^{g_2}\cdots1,0^{g_k}V.
]
Here juxtaposition denotes list concatenation, not binary arithmetic, and the symbols are natural-valued pairs.

## 1. Uniform scanning prefix

The eight ordinary source clauses take 21 steps to move from (G(M,U)) to (EL([0,1],0^{M+1}U)). The zero transfer costs (2(M+1)), so the prepared left stack is (0^{M+2}1) at cost (2M+23). Each next positive-one and DL-zero clause costs 7 and transforms the left stack (0L\mapsto01L). Each transferred zero costs 2. Consequently the whole indicated prefix of (U) can be scanned at cost (7k+2\sum g_i), with result
[
EL(0^{g_k+1}1,0^{g_{k-1}}1\cdots0^{g_1}1,0^{M+1}1,V).
]
This works even when internal gaps vanish.

## 2. Empty remaining suffix

Assume (V=[]) and (g_1,\ldots,g_{k-1}\ge1) (the final gap may vanish). EL-empty costs 1; CR zero sweep costs twice its length. Each CR-one-zero clause consumes a separator zero, adds 3 to the current head on the right and pushes zero, cost 5. The final CR-one-empty clause costs 6. The fixed 47-step return corridor then gives
[
G(M,U)\longrightarrow D_0(2M-3;[2g_1+1,\ldots,2g_{k-1}+1,2g_k+5])
]
for (M\ge5), at total cost (4M+10k+81+4\sum g_i).

If (k=2,g_1=0,g_2=w\ge1), the CR-one-one clause instead produces
[
D_0(2M-5;[3,0,0,0,2w-1])
]
at cost (4M+137+4w). For (w=0) the compact token entry is (H(2M-1,3,[4,1,1,1,0],[])), cost (4M+117), where H uses arbitrary pending tail K after the initial token.

## 3. Next positive entry at least three

Let (V=[v]W), (v\ge3). The EL-positive, DL-add-two, DR-zero sweep and DR-positive pair take (12+4g_k) and restore one extra left zero after removing the newest inserted one. Thus only (g_1,\ldots,g_{k-2}\ge1) are required; the last two gaps may vanish. For (k\ge2), the subsequent CR collection and 47-step return corridor give
[
D_0(2M-3;[2g_1+1,\ldots,2g_{k-2}+1,2g_{k-1}+5]0^{g_k+2}[v-3]W)
]
at cost (4M+10k+89+4\sum g_i+2g_k). For (k=1) the known direct case is (D_0(2M+1;0^{g_1+2}[v-3]W)), cost (4M+99+6g_1).

## 4. Next positive entry equals two

Let (V=[2]W) with the same earlier-gap assumption. Replace the ordinary DR by token DR; its zero sweep produces leading ones. The token CR-one-zero clause pushes a one and increases the following token by 3. Final token CR-one-empty costs 33. The result is a compact token H entry at cost (4M+10k+69+4\sum g_i+2g_k):
- (k=1): (H(2M+5,3,1^{g_1+2}[0],W)).
- (k\ge2): (H(2M+1,3,[2g_1+2,\ldots,2g_{k-2}+2,2g_{k-1}+6]1^{g_k+2}[0],W)).

The arbitrary-tail H subtraction cycle proved in TokenCounterCorrection.append.lean permits quotient batching even with large pending tokens. The H(x,r,K,W) map reduces x by 3, increases r by 4, preserves arbitrary K,W. Its q-cycle cost is (12q^2+(6r+23)q). The ordinary G analogue has cost (12q^2+(6M+27)q). The implementation exact_batch_stack_replay.js uses these two explicit cycles only, without affine period extrapolation.

## 5. Short halting hazards

(G(M,[1,1,1])) halts after (2M+90) steps; (G(M,[1,0,1,1])) halts after (2M+138) steps. Their EL starting forms require only one or two initial left zeros respectively and admit arbitrary untouched left tails. The final source-state reductions are:
- EL(0L,[1,1,1]) -> tok_CR([1,1,1,1,0],[],2L) (65 steps), then halt (2).
- EL(00L,[1,0,1,1]) -> CR(2L,[12]) (113 steps), then halt (2).

SuffixHazards.append.lean contains the source-local proof attempt. These are prepared families, not authentic-root verdicts.

## Executable evidence
- exact_batch_stack_replay.js (4f95e0f8): 2400 two-entry-tail comparisons against the earlier guarded affine replay, all endpoints, costs and halting outcomes agreed.
- adjacent_suffix_arithmetic.js (357d727b): 2222 supported cases, 253 explicitly deferred, no endpoint/cost differences.
- isolated_ones_arithmetic.js (2feaf5a7): 480 cases covering one through six ones and arbitrary positive preceding gaps, including zero penultimate gaps for positive residuals, no differences in exact endpoints/costs versus direct source-cycle batching.
These comparisons are finite tests, not substitutes for the formal derivations. No upper or lower BB(6) bound follows without authentic-root reachability.
