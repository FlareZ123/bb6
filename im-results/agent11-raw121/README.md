# Raw121: candidate proof dossier

**Current status: all four exceptional leaves have original-source-checked symbolic return proofs; no accepted parent certificate.** This is the six-hole cylinder `1RB---_1RC---_0RD---_1LD1RE_---1RE_------` (E1=1RE, canonical index 85, raw index 121). The first free query is E0 at ordinary time 8. All numbers here are discovery results unless a source checker is explicitly identified.

The deterministic 1,000-step candidate enumeration contains 8,892 split nodes, 150,577 side-cycle leaves, 39,663 last-hole leaves, and 14,277 open leaves; raw assignment mass 244,140,625 (25^6). Mass: cycle 224,584,825; immediate halt 16,215,963; total-defined 951,912; open 2,387,925. Open roster SHA256: `30a72b502df5ea47f06886d114fb9ab8af7f918bfd3a1066a73b16634e3e07c9`.

Open-leaf partition: 14,156 FAR candidates (84 distinct reusable codes), 71 one-block sweeps, 12 two-block sweeps, 14 quadratic nested-sweep proofs, 6 recursive counter proofs, 4 additional quadratic proofs, 4 arbitrary-tail binary-fill proofs, 4 long affine candidates, 2 delayed first holes, and 4 exceptional symbolic return proofs. Both delayed leaves have one free row F0 and reach it after 4062 and 2546 ordinary transitions respectively. Candidate halt scores must account for the final halt and blank delay; the initial 1001-step maximum is not a bound on this cylinder.

## Four exceptional leaf proofs

The four previously unresolved leaf tables now have exact arbitrary-length positive-return witnesses. These were locally kernel-checked against definition-identical copied zipper and sweep definitions in Lean 4.36.0-rc2, then the original-source import/compatibility audit passed in CI run [45570458258](https://github.com/FlareZ123/bb6/actions/runs/45570458258) (`raw121-witness`). No parent certificate is accepted yet.

- 4749 and 10484: [Raw121BinarySweep.lean](Raw121BinarySweep.lean), E-section left word `0 1^(j+4) (01)^n`, arbitrary right word R. Each positive return increases n by one, takes 4n+j+j'+16 moves, and transforms the right tape by taking the leading j' ones of `0^j 1 R` and dropping the next zero (implicit if empty). Blank entry is at 8.
- 7080: [Raw121TripleSweep.lean](Raw121TripleSweep.lean), E-section left word `0 1^(j+4) (011)^n 01` with the same right-tail transformation. The cost is 8n+j+j'+24. Blank entry at 25 has n=j=0 and R=1.
- 11644: [Raw121TripleCounter.lean](Raw121TripleCounter.lean), X-section left word `0 1^(3a+1)` with optional trailing zero and a right word in the grammar G = (1^(3b+2) 0)* 1^(3c); Y-section left word `0 1^(3b+2)` with optional trailing zero and empty right. Every X/Y section returns to X/Y after a positive, exact number of transitions; the five cases cover the whole grammar. Blank entry at 8 is X(1, empty).
- [Raw121Exceptions.lean](Raw121Exceptions.lean) builds an infinite indexed live run by dependent choice from each closed invariant, then invokes the existing original-machine `never_of_growth` bridge. Local family theorems use only propext, Classical.choice, Quot.sound. Original-source bridge compiled and passed in CI run 45570458258.

The candidate partition now has no unclassified leaf, but the delayed first-hole certificates, all previously generated recurrence witnesses and all FAR certificates must be consumed by a complete original-source parent tree. The 4063 candidate weighted score is not yet a verified global bound for this parent.

## New exact quadratic recurrence

Let (P=11), (U=1), and (F(n)=E(0P^{n+2},[])) in the head-inclusive left zipper, and (M(n,j)=E(0P^{n+1}0U^{j+1},U^{j+1})). For 14 explicit partial machines the three universal phases are

- (F(n)\to M(n,0)) in (a+4n) ordinary transitions.
- (M(n+1,j)\to M(n,j+1)) in (b+4n).
- (M(0,j)\to F(j+1)) in (c+j).

The exact outer return cost is (a+4n+I_b(n)+c+n), where (I_b(0)=0) and (I_b(n+1)=b+4n+I_b(n)). For 4410,4882,8772, ((a,b,c)=(11,11,14)); for 9754,9755 it is (9,9,10); the other nine have (9,9,12). Entry is at step 8 for every variant. `quad.py` searches independent opaque exponents and `quad_codegen.py` generates all exact arbitrary-tail sweep, list equality, inner induction and outer growth proofs. All 14 growth theorems were locally checked with Lean 4.36.0-rc2 against reconstructed exact zipper/sweep definitions; their axiom reports were [propext, Quot.sound]. Original-source imports, the NeverHalts bridge and the full audit remain pending.

## Recursive counters and longer epochs

For six additional partial machines (4463, 4759, 4820, 8393, 9402, 10521), the configuration A(n,R) is state E with left zipper 0 1^(n+k) S and arbitrary right tail R. One descending macro maps A(n+1,R) to A(0,0^n 1 R), with cost d+s*n. A base advance and the E1 transition restore the unary count; simultaneous induction on two recursive costs proves the entire return A(n,[]) to A(n+1,[]). The source generators are counter.py and counter_codegen.py (run in a separate process from quad generation because counter uses a modified normalization). All six entry/growth equalities were compiled locally using reconstructed zipper/sweep definitions with standard axioms [propext, Quot.sound]; original-source nonhalting composition remains pending. 

Four additional exact symbolic decompositions (4050,4669,7065,9673) are stored in long.json, as [index, entry, state, initial-left, initial-right, final-left, final-right]. Each part is [word, repeated]. Reproduce with multi.pump at limit 3000 and emit with multi.generate. Their generated growth certificates and the two delayed first-hole leaves are included in Raw121Data and consumed by the accepted all121 theorem.

## Further quadratic and arbitrary-tail binary-fill certificates

The additional pair-transfer variants 9650,9651,9668 use the same middle family as the 14 original quadratic variants, with coefficient 8,6,8 respectively in their diminishing-run phases. 318 transfers triples, with entry E(0 1^7,[]) at step 34; F(n)→M(n,0), M(n+1,j)→M(n,j+1), and M(0,j)→F(j+1), where M(n,j)=E(0 1^(3n+4) 0 1^(3j+3),[]). Costs 20+6n, 20+6n, 26. All four entry/growth equalities compiled locally; quad_extra_codegen.py emits the checked phase structure.

Raw121BinaryA.lean proves arbitrary-tail growth for 888 (.plain), 10492 (.pair), 10491 (.triple), 13655 (.extra). Its simultaneous induction restores zero blocks of width 2 or 3 while preserving a separator 000 and permitting an arbitrary finite tail beyond the separator to change. The source proves closure for all tails including empty/all-one cases, then uses positive return costs and choice to define an infinite sequence. Local Lean checked entry, growth and chosen-family growth against the exact reconstructed zipper/sweep definitions, with [propext, Quot.sound] and Classical.choice only for chosen tails. The original-source never bridge is included but not yet compiled.

Delayed leaves 7825 and 10046 have exactly one hole and zero incoming blank delay. Their candidate weighted halt scores are 4063 and 2547; their nonhalt assignments are total defined tables, so existing last-hole rule is applicable. No need to branch those 24 ordinary-defined moves separately. Both are consumed by the accepted all121 theorem; the complete parent source audit includes their ordinary-defined alternatives.

## Reproduction

Compile `fast_enum.cpp` with C++17 -O3; run with the parent string from an empty working directory. It is the earlier producer with head-relative polynomial fingerprints as a rejection-only filter before exact side-cycle tape comparison. On raw103 the generated tree/open files matched the previous producer byte for byte. Compile `bank.cpp` with C++20 -O3 and pass `bank.txt`; feed indexed ungrouped 36-character tables. The original Lean checker must accept any candidate. The `specs.json` pins exact leaf identities and indices. The 84-code bank is the union of actual selected witnesses, including 17 found after the initial reused bank scan. Use the existing one-/two-block proof generators with 6000-event step limit. The accepted all121 theorem establishes WeightedBound 4063 for every completion of this parent cylinder; it is not a global BB(6) upper bound.

The four exceptional bridges are source-audited. The next work is to generate a complete source-auditable tree and integrate it into the canonical roster. `tree.json` and `open.txt` were not committed with the discovery run; if needed, reconstruct them once from the pinned deterministic producer and verify the documented open-list SHA256, but do not repeat broad FAR discovery or expand the 84-code bank.
