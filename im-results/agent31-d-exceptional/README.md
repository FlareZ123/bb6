# Agent 31: a two-return obstruction for the D cryptid's regular F/0 language

**Status (2026-11-03 18:43 UTC): original-source Lean-audited intermediate two-return identity, not a blank-root decision or a new Busy Beaver bound.** The two unbounded raw-transition identities below are a mathematical composition of *previously source-verified Lean theorems*. Their combined `BB6.Agent31SecondSource.two_returns_source` has now compiled against the unmodified source files in manual [CI run 41693590232](https://github.com/FlareZ123/bb6/actions/runs/41693590232) (job 126118179320, head `a76e17029ea375bc039b744dccf51b1cd82d00f6`) and independently in [CI run 41696337587](https://github.com/FlareZ123/bb6/actions/runs/41696337587) (head `12d2ef97208519977bcf1156648f6c8edca9973e`). The exact final theorem axiom audit is `[propext, Quot.sound]`, with no `sorryAx`. These checks establish the *specific all-parameter, two-designated-endpoint theorem* and its dependencies; the full nine-case, third- and fourth-return aggregates and genuine blank-root orbit remain unaudited or unproved as indicated below. The regular-language nonmembership statement and the fixed 442-primitive-step witness have independently passed the local Lean 4.36.0-rc2 kernel with no extra axioms. External originality needs checking.

## Authenticated table, notation and antecedents

The literal six-state two-symbol machine is `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`. Following the project, `I_n(y)` denotes an F/0 configuration with the entire left infinite tape blank and the right tape `1^n y 0^∞`. Explicit finite trailing zeros and implicit infinitely many blank zeros are *observationally* equivalent through Agent32's existing source-certified `source_congr` and `source_pad`; they need not be equal as list objects. Write `P_r=(01)^r`.

The regular family investigated by Agent37 is `L(a,r,b)=I_a(P_r 1^b)` (a≥2, r≥1, b≥0), together with pure unary `I_a`. The first return of an exceptional E-family `L(3k+4,q,1)` usually leaves this regular family; this fact and its one-return source theorem were already known. Here we examine what **a further exact return** does.

Existing, independently Lean-verified source theorems are:

* [Agent35 `full_E_double`](../agent35-cryptid-code/EDouble.lean), [original-source CI 41418613418](https://github.com/FlareZ123/bb6/actions/runs/41418613418): for all k,p,y, the machine sends `I_(3k+4)(0 (10)^(p+1) 1100 y)` to `I_(8k+5)(0 1^(2p+4) 0 1^6 y)` in `12k²+49k+64+4p` primitive transitions.
* [Agent32 `full_E_triple_pairs`](../agent32-cryptid-third/CryptidTriplePairs.lean), [original-source CI 41413674846](https://github.com/FlareZ123/bb6/actions/runs/41413674846): for all K,r,y, `I_(3K+4)(0(10)^r111y)` reaches `I_(8K+9)((01)^(r+2)0y)` in `12K²+49K+58+6r` raw steps.
* [Agent32 exact padding equivalence](../agent32-cryptid-padding/README.md), [CI 41419395469](https://github.com/FlareZ123/bb6/actions/runs/41419395469): the machine evolves identically on physically equivalent right-side trailing-zero presentations.

## Derived all-parameter two-return identity

For **every** t≥0 and q≥3 put k=3t+1, K=8t+3. The exact physical-tape raw dynamics satisfy

```text
I_(9t+7) ( (01)^q 1 )
     --[ 12k² + 49k + 56 + 4q ]-->
I_(24t+13) ( 0 1^(2q) 0 1^6 )
     --[ 12K² + 49K + 58 ]-->
I_(64t+33) ( (01)^2 0 1^(2q-3) 0 1^6 ).
```

**Proof.** Since `(01)^q 1` is physically the same right tape as `0(10)^(q-1)1100` for q≥2, apply `full_E_double k (q-2) []`; simplify the arithmetic and trailing-blank equivalence. The intermediate unary length satisfies `24t+13=3(8t+3)+4`. Its right suffix decomposes exactly as `0 [111] [1^(2q-3) 0 1^6]`, matching the complete triple-pairs theorem with zero alternating-pair tokens. Apply `full_E_triple_pairs K 0 (1^(2q-3) 0 1^6)`. The final exact symbolic equality follows. All ingredients have arbitrary untouched suffixes and use the same physical transition convention. This is a finite composition of two source theorems for arbitrary natural parameters.

**Regular-language obstruction.** For q≥3, `2q-3≥3`; the final suffix has a `110` occurrence before the final zero followed by six ones. No word of the form `(01)^r 1^b` contains `110`: in the alternating prefix every one is followed by zero except possibly the final one, after which only ones occur. Therefore the final right suffix is outside Agent37's L, for **all** t≥0 and q≥3. The quantifier-unbounded list inequality is independently checked by Lean's theorem `BB6.Agent31Language.second_escape_not_regular` in [EscapeLanguage.lean](./EscapeLanguage.lean), axiom audit `[propext, Quot.sound]`. An equivalent recognizer-based proof is kernel-checked.

**Scope:** This refutes the universal synthetic statement that two E-section returns always restore the L grammar, even in the residue subfamily k≡1(mod3). It does **not** prove that any original blank-root trajectory enters one of these special input tapes, and cannot decide whether a true blank-root machine halts. The two source theorems guarantee exact forward endpoints; their combination here does not assert that no intermediate physical F/0 section occurs for arbitrary t,q.

## Fully independently kernel-checked minimal witness

Set t=0, q=3: the input is `I_7(0101011)`, first physically blank-left F/0 at transition 129 is `I_13(0 1^6 0 1^6)`, and the second at another 313 transitions is `I_33(01010 1^3 0 1^6)`, after total 442. The final suffix is outside L. [EscapeWitness.lean](./EscapeWitness.lean) implements the literal full 11-live-action table and a frozen halt state and proves `first_return_129`, `second_return_313`, `two_returns_442`, and the absence of any earlier positive-time physically blank-left F/0 returns on both segments, via kernel reduction (`by decide`). All five theorem axiom audits say **no axioms**. The theorem concerns an explicitly **synthetic** F/0 start.

The independent Python [check_second_escape.py](./check_second_escape.py) stores a sparse physical tape and independently checks the two actual first physical F/0 returns against the derived formula for t=0..4, q=3..11: **45/45 matches** including complete right tape, times, state and blank-left guard. This is bounded corroboration, not an all-parameter proof.

## Blank-origin numerical caveat and next goal

An independent arithmetic interpreter of Agent37's eleven source-derived one-future-return rules, using only the canonical L shapes, first reaches an E-exceptional `b=1` state from the four authentic D-family unary seeds at conditional iteration indexes 1711 (seed5, q5), 8394 (seed9, q6), 9458 (seed15, q9), and 7611 (seed39, q7). These indices are **computational predictions**, not original-machine kernel-checked root certificates. At the first exception, the `k=(a-4)/3` values have residues 0,0,0,2 modulo3, respectively, so the two-return k≡1(mod3) obstruction above is **not** a verified first-exception consequence for those four blank-root runs. The entire source grammar composition, the physical-root bridge, and possible missing earlier returns must be audited before upgrading this observation.

Further work of highest value: source-import the combined two-return theorem and a genuine blank-orbit certificate, then investigate whether E escapes induce a larger *closed reachable language* capable of distinguishing the forbidden F/1 halt gate. Avoid generalizing from this restricted two-return obstruction to unconditional machine nonhalting.

**Reproduce:** Lean 4.36.0-rc2, compile both `.lean` files directly from a fresh working directory; Python 3.11+ runs `check_second_escape.py` without third-party packages. No custom per-commit CI is needed.


## All exceptional E inputs: complete nine-case two-return formula (12:50 UTC)

The more complete source-derived result is [two-return-classification.md](./two-return-classification.md). It covers **all** `I_(3k+4)((01)^q1)` with k≥0, q≥1, including the three k residues and q modulo3, yields explicit exact primitive-step costs for both endpoints and identifies exactly one class of two-section outputs outside L: `k≡1 (mod3), q≥3`. Full nine-case formulas are in that document. This is a genuine all-parameter mathematical composition of earlier source-certified raw-machine macros, awaiting **consolidated** original-source Lean import and external novelty assessment.

The independently authored raw transition checker [check_all_E_second.py](./check_all_E_second.py) verified **144/144** first/second physical F/0 complete tapes and exact primitive-step times for k=0..11, q=1..12, with **40 outside L** precisely in that condition.

[extended_conditional_orbit.py](./extended_conditional_orbit.py) joins the nine-case E exception escape map to Agent37's original eleven-rule conditional L macro table. Starting at the four certified D-family unary *entry seeds* (5,9,15,39), the **first conditional checkpoint after which the L grammar cannot represent the resulting section** occurs as follows:

| Authentic unary seed | Conditional index of E-exception input | E index k residue | q | Input unary bit-length | SHA256 of unsigned little-endian input a |
|---:|---:|---:|---:|---:|---|
| 5 | 6,389 | 1 | 4 | 9,044 | `5e2acebd56d6366b3b4c8477753d1fc1fc56ea53f13900abe26b32913b8a1133` |
| 9 | 31,787 | 1 | 4 | 44,984 | `a1c93524b11ca66d4f419ec54b22b41a0cdc250d90003a99932a85e6d65dda80` |
| 15 | 12,689 | 1 | 4 | 17,960 | `978d993556ed3495803c9ae36cc06dab52e6178580e182bf93c9694804b035d2` |
| 39 | 9,838 | 1 | 8 | 13,927 | `28384913d91f238f6838ec49371045d7fe50c24f04f3e0e5df312ce6b3844fd0` |

The arithmetic code checks its own exact two-step exceptional map against all 144 raw-derived short cases. These large-index predictions are **conditional symbolic forecasts**, not individually source-certified authentic blank-run events. The table has no implied upper or lower bound for BB(6). The original-source composition and true-root reachability obligations remain open.


## Third return and residue-sensitive closure (12:55 UTC)

[third-return-classification.md](./third-return-classification.md) derives, from prior quantified original-machine source macros, the **third** exact physical F/0 checkpoint for the sole two-return-exception family `I_(9t+7)((01)^q1)` (q≥3). Write `k=3t+1`; the third output is again inside regular L for *every* q when `k≡1 (mod9)`; the other residues k≡4,7 (mod9) produce two explicitly described non-L packet families. This five-row case table and all elapsed primitive-step counts are in the linked report. The independent [third_conditional_orbit.py](./third_conditional_orbit.py) verifies **100/100** exact third physical returns on t=0..9, q=3..12 with the literal raw table.

The same script gives the updated earliest **conditional** still-off-L milestones after allowing a third return for k≡1(mod9): seed5 index **19758** (q7, k mod9=4), seed9 index **31787** (q4, k mod9=7), seed15 index **20855** (q4, k mod9=4), seed39 index **18820** (q8, k mod9=4). All are conditional arithmetic projections with giant unary parameters and are **not** original blank-tape proof checkpoints. Source-composition Lean import and external novelty assessment remain necessary. The challenge shifts to the two new packet families at k mod9∈{4,7}.


## Original-source verification update (18:43 UTC)

Both manual CI runs above completed successfully on GitHub-hosted runners, with the actual Lean compiler executing on the original checked-in dependency chain (`Boundary.lean` restored with the repository hash check, `CryptidSix`, `CryptidPairs`, `CryptidTriplePairs`, `EDouble`, `Generic`, and `BoundaryPadding`). In run 41693590232 the log printed `[propext, Quot.sound]` for `first_source`, `second_source` and `two_returns_source`, and `PASS 45 independent exact two-return checks`. This repairs the earlier CI-pending provenance of `ESecondSource.lean`. The exact source object uses observational equivalence of tapes at the combined endpoint and does not assert universal earliest-return minimality. The simulation sample additionally checked first-return minimality only for its 45 finite cases. The nonregular suffix statement is a separate universal Lean theorem. Neither source compilation nor that language theorem proves reachability of these inputs from the original blank-tape root.
