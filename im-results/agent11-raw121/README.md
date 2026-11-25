# Raw121: candidate proof dossier

**Current status: 13 unresolved leaves, no accepted parent certificate.** This is the six-hole cylinder `1RB---_1RC---_0RD---_1LD1RE_---1RE_------` (E1=1RE, canonical index 85, raw index 121). The first free query is E0 at ordinary time 8. All numbers here are discovery results unless a source checker is explicitly identified.

The deterministic 1,000-step candidate enumeration contains 8,892 split nodes, 150,577 side-cycle leaves, 39,663 last-hole leaves, and 14,277 open leaves; raw assignment mass 244,140,625 (25^6). Mass: cycle 224,584,825; immediate halt 16,215,963; total-defined 951,912; open 2,387,925. Open roster SHA256: `30a72b502df5ea47f06886d114fb9ab8af7f918bfd3a1066a73b16634e3e07c9`.

Open-leaf partition: 14,156 FAR candidates (84 distinct reusable codes), 71 one-block sweeps, 12 two-block sweeps, 14 quadratic nested-sweep proofs, 5 recursive counter proofs, 4 long affine candidates, 2 delayed first holes, 13 unresolved. Both delayed leaves have one free row F0 and reach it after 4062 and 2546 ordinary transitions respectively. Candidate halt scores must account for the final halt and blank delay; the initial 1001-step maximum is not a bound on this cylinder.

## New exact quadratic recurrence

Let (P=11), (U=1), and (F(n)=E(0P^{n+2},[])) in the head-inclusive left zipper, and (M(n,j)=E(0P^{n+1}0U^{j+1},U^{j+1})). For 14 explicit partial machines the three universal phases are

- (F(n)\to M(n,0)) in (a+4n) ordinary transitions.
- (M(n+1,j)\to M(n,j+1)) in (b+4n).
- (M(0,j)\to F(j+1)) in (c+j).

The exact outer return cost is (a+4n+I_b(n)+c+n), where (I_b(0)=0) and (I_b(n+1)=b+4n+I_b(n)). For 4410,4882,8772, ((a,b,c)=(11,11,14)); for 9754,9755 it is (9,9,10); the other nine have (9,9,12). Entry is at step 8 for every variant. `quad.py` searches independent opaque exponents and `quad_codegen.py` generates all exact arbitrary-tail sweep, list equality, inner induction and outer growth proofs. All 14 growth theorems were locally checked with Lean 4.36.0-rc2 against reconstructed exact zipper/sweep definitions; their axiom reports were [propext, Quot.sound]. Original-source imports, the NeverHalts bridge and the full audit remain pending.

## Recursive counters and longer epochs

For five additional partial machines (4463, 4759, 8393, 9402, 10521), the configuration A(n,R) is state E with left zipper 0 1^(n+k) S and arbitrary right tail R. One descending macro maps A(n+1,R) to A(0,0^n 1 R), with cost d+s*n. A base advance and the E1 transition restore the unary count; simultaneous induction on two recursive costs proves the entire return A(n,[]) to A(n+1,[]). The source generators are counter.py and counter_codegen.py (run in a separate process from quad generation because counter uses a modified normalization). All five entry/growth equalities were compiled locally using reconstructed zipper/sweep definitions with standard axioms [propext, Quot.sound]; original-source nonhalting composition remains pending. 

Four additional exact symbolic decompositions (4050,4669,7065,9673) are stored in long.json, as [index, entry, state, initial-left, initial-right, final-left, final-right]. Each part is [word, repeated]. Reproduce with multi.pump at limit 3000 and emit with multi.generate; those full Lean growth certificates remain to be checked. The two delayed first-hole leaves are to be certified using the existing last-hole rule, including the ordinary-defined alternatives.

## Reproduction

Compile `fast_enum.cpp` with C++17 -O3; run with the parent string from an empty working directory. It is the earlier producer with head-relative polynomial fingerprints as a rejection-only filter before exact side-cycle tape comparison. On raw103 the generated tree/open files matched the previous producer byte for byte. Compile `bank.cpp` with C++20 -O3 and pass `bank.txt`; feed indexed ungrouped 36-character tables. The original Lean checker must accept any candidate. The `specs.json` pins exact leaf identities and indices. The 84-code bank is the union of actual selected witnesses, including 17 found after the initial reused bank scan. Use the existing one-/two-block proof generators with 6000-event step limit. No claim is made yet that all assignments satisfy a fixed score bound.

The next work is to prove the remaining 13 explicit exceptions or classify them as delayed first holes, then generate a complete source-auditable tree and integrate it into the canonical roster. Do not repeat the raw121 initial enumeration or broad FAR search.
