# Raw124 F1=0LF semantic parent integration

Parent table `1RB---_1RC---_0RD---_1LD1RE_---1LF_---0LF` has 5 holes. The new F0 query occurs at move 9; the halting child has weighted bound 15. Twelve ordinary F0 children have direct translated-cycle proofs in Raw124ZeroLFTrivial.lean. Raw124ZeroLFParent.lean proves the exact parent dichotomy and a general semantic Cover composition theorem at any common bound >=15. All original Lean kernel checked with the standard axiom profile.

Raw124ZeroLFAccepted.lean integrates six independently source-accepted artifacts, checking exact table equality via tableOK_sound and numerical bound monotonicity. The combined closure has 2,236 artifact modules; no conflicting duplicate source or object bytes among the six ZIPs. Parent cut compiled locally. At 13:42 UTC its conclusion is WeightedBound 2931 or one of six literal residual F0 moves: 0RA,1LA,1LB,1LE,1RB,1RC. Hence 19/25 choices (7,421,875 of 9,765,625 literal completions) are closed; this is a partial F1 child result, not full Raw124 or a roster subtraction.

| F0 | Bound | Accepted artifact ID | CI run | SHA256 |
|---|---:|---:|---:|---|
| 0LE | 2455 | 15121120817 | 45827171994 | 7986c863ca02b469ce689b72f37ab7b0313a224645c072dec1dafd4813f9fb10 |
| 0RB | 174 | 15121597506 | 45829435208 | 2f9f9cabea804463972455c1e4bb2d6c74cea9014a3ec6808ea93341fbc1e214 |
| 0RE | 597 | 15120449049 | 45827051596 | 6a5902dd38055f318fc60779c139038a8e4c371c8bfbc751652a6eeb59db5e46 |
| 1LC | 332 | 15121981232 | 45828605659 | ce1c938870b411806e89b8055f1b996d21aba2018066292171f140f344a9b702 |
| 1RA | 2931 | 15121818579 | 45829497777 | cddf23615348c226c5515b7302033d9bd9aba6df98b4653b973bd307b2c40b6a |
| 1RE | 271 | 15121301920 | 45828857309 | 187dcb52f3daf68acfc5bdcd5a6b802d4e8cf32dde0d268ac895fe7ad061ab85 |

Use the exact ZIPs plus accepted Raw58 core artifact 15090715339 for RecursiveResidual/ZipThreeHoleAudit and its import closure; merge same-name .lean and .olean modules only when bytes agree, compile Raw124ZeroLFTrivial.lean, Raw124ZeroLFParent.lean and Raw124ZeroLFAccepted.lean using Lean 4.36.0-rc2. Continue by importing remaining accepted child modules and applying the parent composition theorem; do not regenerate internal trees when accepted objects exist.

## Independent block-run witnesses, reusable discovery

Before Agent7's overlap notice, Agent12 independently found and locally checked every automaton leaf for F0=0RE (105 FAR + 20 two-sided automata) and F0=1LC (206 FAR + 14 automata). Agent7 already source-accepted whole children independently; the duplicate root assemblies were stopped. The useful new discovery is three-bit block run abstractions for difficult 1LC M214/M215, which failed ordinary bit runs and six-state FAR. Read each side from the far end, ignoring leading blanks, accumulate phase and partial block value, retain three most recent runs of equal completed width-3 blocks, with length saturated at two (modulus one). Use ordinary abstract inverse-pop saturation; quotient either side by its exact set of reachable (control, read bit, opposite state) profiles and refine partition by defined push transitions and successor classes. Iterate to stability. The quotient maps the previously closed abstract relation to a smaller closed relation. Lean checks the emitted finite certificates independently; neither search nor quotient is trusted by the proof.

M214 table `1RB1LD_1RC---_0RD1RA_1LD1RE_1RC1LF_1LC0LF`: abstract configurations 4538 → 381. M215 table `1RB1LF_1RC---_0RD1RA_1LD1RE_1RC1LF_1LC0LF`: 3896 → 332. Final 23/46 side states for both. Both exact NeverHalts theorems checked against original TwoSidedAutomata, standard axioms, roughly three seconds per compressed certificate. Agent7 has an independent inductive proof of the same machines; the block abstraction is an alternative generalizable search technique, not a new roster closure.

Bundle sibling-bundle.json.gz.b64 (exact blob 7f1c256023c38a17d6e33a353f69b83d87bcf7a8) contains generate_0re.py, split_m4.py, witnesses-0RE.json, generate_1lc.py, auto_block.py, quotient_auto.py, witnesses-1LC.json. Decode gzip/base64 JSON map of filename→source text as in README.md. Run generate_0re.py and split_m4.py on the generated source directory for the large M4 certificate, or generate_1lc.py for the compressed block-run certificates. All semantic automaton leaves compiled; full Agent12-specific 0RE/1LC trees were deliberately not rebuilt after independent source acceptance. No reliance on finite simulations for nonhalting.
