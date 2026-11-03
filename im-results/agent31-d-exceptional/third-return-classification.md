# Third D cryptid return: a precise residue-dependent restoration / obstruction

**Status 2026-11-03:** all-parameter source-theorem composition with a 100-case independent raw-TM test, original-source *combined* Lean compilation pending. This concerns synthetic F/0 entries. It is not an exact BB(6) result, a root decision or a certified blank-orbit itinerary.

Use the same original D table and notation as [the two-return classification](./two-return-classification.md). That proof establishes the sole two-checkpoint exception:
```text
I_(9t+7)((01)^q 1) --T1--> I_(24t+13)(0 1^(2q) 0 1^6)
    --T2--> I_(64t+33)((01)^2 0 1^(2q-3) 0 1^6)
```
for all t≥0, q≥3. We now classify the **third** exact physical F/0 checkpoint for all these inputs, using the existing original-source universal B/A-code/A110111/E-triple-pairs theorems. Let p=2q-3≥3, write t=3u+s.

| s=t mod3 | Third exact F/0 endpoint | L status | Third step count |
|---|---|---|---|
| 0, q=3r | `I_(8K+13+16r)` | pure unary | `P+C+2(m+d)+6` |
| 0, q=3r+1 | `I_(8K+7+16r)((01)^3 1^2)` | in L | `P+C+2(m+d)+24` |
| 0, q=3r+2 | `I_(8K+33+16r)` | pure unary | `P+C+2+6(m+d+1)+41+6(m+d+5)+41+2(m+d+9)+6` |
| 1, all q≥3 | `I_(8K+9)((01)^4 0 1^(2q-6) 0 1^6)` | outside L | `12K²+49K+70` |
| 2, all q≥3 | `I_(8K+10)(0101^(2q-3)0 1^6)` | outside L | `12K²+49K+40` |

For s=0 set `K=64u+10`, `m=4K+3`, `P=12K²+41K+32`, `v=floor((2q-3)/3)`, `d=2+4v`, `C=4+v(6(m+2)+41)+12v(v-1)`. The q=3r and 3r+1 rows have r≥1, as does q=3r+2 since q≥3. In the s=1 row `K=64u+31`; in s=2 `K=64u+53`. These are elapsed primitive transitions starting from the **second** F/0 output, in addition to T1 and T2.

**Derivation.** When t≡0 mod3 the second checkpoint has 3K+3 leading ones and enters the source-certified A branch. The suffix after the initial zero starts with two code tokens `10`, then v triple-`111` tokens. If p mod3=0, it closes on the following zero and absorbs the six trailing ones into the unary section. If p mod3=2, the original all-code `110111` theorem leaves exactly `01010 111 = (01)^3 1^2`. If p mod3=1, consume an additional `10` and two `111` tokens before implicit-blank closure, again producing pure unary. The exact token cost formula C counts the two leading `10` tokens and all v following triples.

When t≡1 mod3 the second checkpoint has 3K+4 leading ones. The previously checked `full_E_triple_pairs K 2` consumes `0(10)^2 111` and leaves `(01)^4 0 1^(p-3) 0 1^6`. When t≡2 the section has 3K+2 leading ones, and `full_B` consumes the first zero and merges its first remaining one into the unary prefix. Both outputs still have an internal `110` or `00` separating nonalternating packets, hence are outside L for q≥3.

**Consequence:** In the two-return-exception subfamily, *three* source-macro checkpoints recover L for every k≡1 mod9, any q≥3. The other two residues k≡4,7 mod9 retain explicit off-language packets. No earlier-return minimality is asserted by this composition.

## Independent exact physical machine validation

[third_conditional_orbit.py](./third_conditional_orbit.py) independently simulates the full literal original 11-live-transition machine, checks 100 exact third physical F/0 outputs for t=0..9 and q=3..12, and matches the five rows above including complete right words. **100/100 passed**. The script also composes the already checked eleven L cases and nine E-exception two-step cases, with a third-step return to L whenever k≡1 mod9, without claiming the resulting giant modeled root itinerary is formally source-certified.

The earliest conditional remaining off-language **after allowing up to three E-exception return checkpoints** becomes:
- Seed I5: E exception input at checkpoint 19,758, k≡4 mod9, q=7, input a bit-length 27,962, SHA256 unsigned little-endian a `5dda73a6d6d3104525aa092785eb96e687524aded2982b1ec48f3a21575a140d`.
- Seed I9: checkpoint 31,787, k≡7 mod9, q=4, input a 44,984 bits, SHA `a1c93524b11ca66d4f419ec54b22b41a0cdc250d90003a99932a85e6d65dda80`.
- Seed I15: checkpoint 20,855, k≡4 mod9, q=4, input a 29,515 bits, SHA `2a6cd016f4f36d651b92c0ee50b6f18c7e1b877d16ba3d37657649d3e492bd3f`.
- Seed I39: checkpoint 18,820, k≡4 mod9, q=8, input a 26,637 bits, SHA `c1dabcf62aff0a1173c8a25cf0c22fffdd39d617e14da6ce620bae00c5cae9a8`.

These are **conditional model indices only**. They are stronger diagnostics for language design, not actual blank-run certificates; original source import and a root-connected induction remain unavailable. The external @-d simulation is known to extend far beyond these section counts. No external novelty claimed.

## Next scientific direction

Introduce a finite collection of auxiliary word shapes `(01)^4 0 1^p 0 1^6` and `0101^p0 1^6`, prove a uniform source-derived next-section map for their leading unary residue, and test closure against physical F/1 halt gates. Alternatively, establish a mathematically precise limitation on bounded return-group regular-language closure. Preserve the distinction between a conditional source-rule chain and an authenticated all-time blank-root induction.


## Fourth checkpoint: two exact infinite subfamilies

The certified B-return, after the preceding E and B/A word transformations, gives two further parameter-unbounded fourth endpoints for every v≥0 and q≥3 (write P_r=(01)^r):

* k=27v+4: the third F/0 section is I_(1536v+257)(P_4 0 1^(2q-6) 0 1^6). The fourth return costs 12K²+49K+40 with K=512v+85, and yields I_(4096v+690)(P_3 0 1^(2q-6) 0 1^6).
* k=27v+7: the third F/0 section is I_(1536v+434)(0 1 0 1^(2q-3) 0 1^6). The fourth return costs 12K²+49K+40 with K=512v+144, and yields I_(4096v+1162)(0 1^(2q-3) 0 1^6).

Both fourth right words remain outside L. Their universal language exclusions were checked locally in Lean 4.36.0-rc2: `fourth_escape_A_not_regular`, `fourth_escape_B_not_regular` in [EscapeLanguage.lean](./EscapeLanguage.lean), with axioms [propext, Quot.sound] only. The independent literal-machine [fourth_branch.py](./fourth_branch.py) verifies exact third and fourth full physical tapes and primitive times for 12 cases v=0..1, q=3..5.

This is a finite-depth, source-derived 3-adic obstruction: two L checkpoints can fail for k≡1 mod3; three checkpoints can fail for k≡4,7 mod9; four checkpoints can fail for k≡4,7 mod27. No induction proves an obstruction for arbitrary depth, and the actual blank-root machine remains undecided. The composed fourth-return identity still awaits an end-to-end authentic original-source Lean check.
