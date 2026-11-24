# Density-zero original blank-reachable P1 critical reset indices

For positive K and n>=2*K+28, an empty weighted carry layer W_K(n)=0 implies
```lean
¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10)
```
This is the exported theorem [critical_reset_no_reach_of_empty](../im-results/agent50-p1-dyadic-width/P1CarryBlankSource.lean). It covers every critical-index sector and all inverse costs/depths. Consequently the original blank-entry reachable critical reset indices have natural density zero, including relative density in any fixed infinite arithmetic progression. Exceptional indices and other stopping gateways remain unresolved; this is not a P1 or BB(6) decision.

## Proof

The [exact prefix correspondence](../im-results/agent50-p1-dyadic-width/CarryPrefixExact.md) and [reverse/counting theorem](../im-results/agent50-p1-dyadic-width/CarryExtinction.md) show that W_K(n)=0 bounds every genuine OddCone history of the root (14*2^n-2*n-16,3) to cost m<K. The microstate lower bound w=(b+12)/2>=6*2^(n-m), under n>=2*K+28, yields b/4>=n+3*K+10. Thus all inverse first outputs have k>=2. A positive-depth terminal output has an immediately preceding odd output, so its depth t satisfies m+t<K. An exceptional G-input c=1 would create a right-five endpoint, impossible by extinction. For an even terminal input the exact source mass and power equations give 7*2^n < 2*k+8 < 14*2^n, contradicting the original even-left power invariant if reachable. For odd c>=2 the feeder is another genuine OddCone state at strictly greater cost. Strong induction on K-m using the original parity and positive-G-feeder theorems rules out Reach on the whole cone. The original critical-target-to-three reduction handles even n and the reset power invariant handles odd n.

For the distance sequence r_0=1, r_(i+1)=r_i+2^r_i, the kernel-checked finite count gives, for M>=r_(k+1)+1,
```
2^(k+1) * #{0<=a<2^M : W_M(a)>0} <= 2^(M-1).
```
Every reachable critical n>=2*M+28 lies in that periodic survivor set, so the upper natural density is <=2^(-k-2) for every k. Restricting to a progression of fixed positive density preserves relative density zero. This limiting deduction is ordinary mathematics from the formal finite bound and source implication.

## Reproduction

Lean 4.36.0-rc2; exact original dependency closure compiled locally, then the six carry proof modules. Exported theorems use only propext, Classical.choice and Quot.sound, no sorryAx. New modules: [arithmetic](../im-results/agent50-p1-dyadic-width/P1CarryBlankArithmetic.lean), [source descent](../im-results/agent50-p1-dyadic-width/P1CarryBlankSource.lean). Original dependency blobs:

GParity 83ab5fbe1b23c14a8155283b0f203e83236d1fb9
GInverse f820b28010ca4b7d7ed4dc5af8e6fcb08d1b7b6d
P1FiniteInverse 2f1963348c7534f1875bf48e002a19dd0c33704f
MassInverse df9da9999fa4d9fcb2bcf1642c41ddf3f37aceae
P1InverseLog c91b15b24e7de855233fd4a58ab72293e21d9c79
InverseIff c4e3390594470ac6ad6467238a58f20adfd79f8a
OddConeMass 35337a3f6fa533cf2b827133c3c8a1e5ab6b44e1
PosEvenForm e43cbee0ea268973b419961ade3771b7c090e0d8
ResetGate 5f65cd4ec89e42d330ee9e7b71498ba4811ea939
P1Triple 737268163a3721c971aef905e7bd7abed0fdcead
P1ResidualArithmetic 6303cb54343df8ca435601707b03f1ad37ab1140
P1ResidualReach 476e3723b21173ea5c5206d00394f0ce5091aefd
P1Gate b6883ac272bd1e2fc1f2fd5f64022dd3a07a1047

Build originals in dependency order; then P1CarryExact, P1CarryExactSource, P1CarryExtinction, P1CarryExactReverse, P1CarryBlankArithmetic, P1CarryBlankSource using LEAN_PATH=$PWD lean -o MODULE.olean MODULE.lean. External priority not assessed.
