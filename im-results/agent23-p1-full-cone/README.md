# Full-cost P1 critical-cone terminal certificate

Agent 23, 2026-11-24. Status: standalone arithmetic/checker kernel-verified with Lean 4.36.0-rc2, n=30 certificate verified by kernel reduction, six exact C++ certificates passed; generic reachability composition kernel-verified under explicit source premises; original-source instantiation and n=30 exclusion fully kernel-verified. This extends the endpoint test of Agent28/43 and the early-extinction closure of Agent50. It does not decide P1 or BB(6).

## Criterion and proof

Let P=2^n, Q=7P-(n+3), n>=14. Start the full carry recurrence (Agent28 ExactEndpoint) with [1] at j=0. Each carry v produces v/2 if v even and (v+Q-j)/2 if v+Q-j even. Keep both branches including multiplicities.

Suppose there is K>0 such that layer K is empty, and every carry v at every layer j<K satisfies

    v != 2
    v+2*j+2*n+3 < 7*P.

No restriction K<=n is needed. Then the original critical hub (14P-2n-16,3) cannot be Reach.

Proof using the accepted original-source endpoint and feeder theorems:
1. For every OddCone state (b,d,m), source_endpoint gives v=(d-1)/2 in layer m by direct OddCone induction; empty-layer absorption gives m<K. The source mass is b+d+2m+2n+13=14P, d odd. The strict margin implies b>=12, so every inverse output has k>=2 by inverse_k_lower. In particular b is not the small-left reset.
2. If an inverse had c=1, it would produce an OddCone child at d'=5 with carry 2, contradicting the first test.
3. For a potential positive-even feeder, c is even and the source equations give d+b/2+3=2^t(c+3) and 2k+c+2t+1=b+d (b divisible by 4). Parity forces t>=1. inverse_prev_odd gives a depth-(t-1) inverse with odd c0; its power equation implies c0+3=2(c+3). Its genuine OddCone child has cost l=m+t and carry y=(c0+3)/2=c+3. The source even mass equation becomes 2k+c+2l+2n+14=14P. The checked margin at (l,y) now implies 7P<2k+8<14P. No number of form 14*2^a lies in that open interval. This excludes even_left_power_shape for the proposed reachable feeder.
4. Assume a reachable cone state. Its even left coordinate and b>=12 force b%4=0 by reachable_even_mod4. With c=1 excluded, positive_G_feeder supplies a reachable predecessor (2k-4,c+4). Even c is excluded by step 3. Odd c instead gives a genuine OddCone child with larger cost, still <K. Strong induction on K-m gives a contradiction. For even n, critical_target_implies_three transports this hub exclusion to the reset Reach 2 (14P-2n-10).

The check is stronger than just excluding carry 2. It handles the other actual exit of the source feeder theorem and small-left escape at once. The entire original-source composition is kernel-verified. The generic reachability composition is now fully kernel-checked in FullConeCertLogic.lean, including both terminal cases and strong induction. ConeFacts makes every source obligation explicit; no axioms or sorry are introduced. FullConeCertSource.lean instantiates all premises against the actual source imports and proves source_critical_reset_no_reach and source_critical30_no_reach.

## Computation

The previously identified six residual indices below 10000 all pass the stronger complete-cone test. The observed first empty layer and peak list size:

| n | K | peak |
|---:|---:|---:|
|30|82|44|
|286|1442|504|
|350|586|152|
|1614|5824|1544|
|2990|6154|3040|
|3342|13730|7488|

Reproduce with g++ -std=c++17 -O3 full_cone_scan.cpp -o full_cone_scan && ./full_cone_scan (Boost multiprecision headers). The executable checks every list entry with arbitrary precision, no pruning, no deduplication and no floating-point arithmetic. All six printed OK.

FullConeCertCore.lean locally compiles with Lean 4.36.0-rc2. cert_sound, safe_left, safe_even_gap, previous_odd_carry and no_power have only ordinary Lean axioms (propext, Classical.choice where needed, Quot.sound); cert30 has no axioms. Direct kernel reduction of larger certificates exceeded local short execution limits; use efficient verified representation or existing manual CI, not new per-lemma workflows. The other five certificates remain computational evidence, not kernel proofs.

## Integration and reproduction

Direct local Lean 4.36.0-rc2 compilation succeeded using unchanged GitHub blobs fetched through the connector (local Git DNS was unavailable). The direct OddCone induction avoids importing CountCone or P1CarryWideSource. Copy these originals in the listed compile order to a scratch directory and compile each with `lean -o Module.olean Module.lean` with LEAN_PATH including that directory:

| Module | Git blob SHA |
|---|---|
| GParity | 83ab5fbe1b23c14a8155283b0f203e83236d1fb9 |
| GInverse | f820b28010ca4b7d7ed4dc5af8e6fcb08d1b7b6d |
| PosEvenForm | e43cbee0ea268973b419961ade3771b7c090e0d8 |
| ResetGate | 5f65cd4ec89e42d330ee9e7b71498ba4811ea939 |
| P1FiniteInverse | 2f1963348c7534f1875bf48e002a19dd0c33704f |
| MassInverse | df9da9999fa4d9fcb2bcf1642c41ddf3f37aceae |
| OddConeMass | 35337a3f6fa533cf2b827133c3c8a1e5ab6b44e1 |
| P1InverseLog | c91b15b24e7de855233fd4a58ab72293e21d9c79 |
| P1Triple | 737268163a3721c971aef905e7bd7abed0fdcead |
| P1ResidualArithmetic | 6303cb54343df8ca435601707b03f1ad37ab1140 |
| P1ResidualReach | 476e3723b21173ea5c5206d00394f0ce5091aefd |
| P1Gate | b6883ac272bd1e2fc1f2fd5f64022dd3a07a1047 |

Paths: GParity/GInverse/PosEvenForm/ResetGate in agent1-p1-map; P1FiniteInverse/P1InverseLog in agent47-p1-finite-inverse; MassInverse/OddConeMass in agent1-p1-quarter; P1Triple/P1ResidualArithmetic/P1ResidualReach/P1Gate in agent50-p1-residue (all under im-results). Compile FullConeCertCore, FullConeCertLogic, FullConeCertSource in that order. Final theorem source_critical30_no_reach has axioms [propext, Classical.choice, Quot.sound] only. No new CI workflow or native_decide used in the accepted result. Source commit caa684912358229e46bb802abeda8292c7ea407e. 

The direct endpoint block equation follows Agent28 ExactEndpoint, adapted to OddCone. Agent50 positive_G_feeder and critical_target_implies_three provide the genuine original reachability reduction. The other five numerical checks remain to be kernel-certified. This does not decide P1 or BB(6).

## Segmented kernel certification

FullConeCertChunks.lean proves cert_append and cert_join. For n=350, generate exact boundary lists at every 8 layers (untrusted Python generator); 74 segments each prove safety by decide and exact successor-list equality by rfl. Independently compile 10 Part modules then join via cert_join from the empty final layer. All compiled locally on Lean 4.36.0-rc2; source_critical350_no_reach reports [propext, Classical.choice, Quot.sound] only. The checked first version used namespace BB6.Agent23FullCone; the reusable generator isolates each n in a separate subnamespace to prevent name collisions. Reproduce by running python generate_chunks.py 350 586 8, then compile FullConeCertChunks, Cert350Data, all Cert350Part*.lean, and Cert350Proof with LEAN_PATH containing the output directory and the earlier original dependency closure. No native_decide used in either accepted n=30 or n=350 exclusion. Native evaluations for n=286,1614,2990 succeeded separately but use compiler-trust axioms and are not counted as kernel-only results. Four of the six indices still need kernel-only proofs.
