# Raw123: candidate weighted partition

Canonical index 87, raw index 123 in the canonical-124 manifest. Parent `1RB---_1RC---_0RD---_1LD1RE_---0RF_------`. First unknown transition F1 at normalized step 7.

The reproducible candidate enumeration partitions all 25^6 = 244,140,625 full completions. There are 16,817 split nodes, 306,928 cycle leaves, 68,320 last-hole leaves, and 11,544 initially open leaves. The compact manifest gives 11,211 FAR, 225 symmetric n-gram, 23 asymmetric n-gram, 37 single-block and 26 multi-block growth candidates, and nine late last-hole queries. The 13 explicitly unresolved one-hole leaves represent 325 full completions. A late first-hole query at step 9,108 in table `1RB0LF_1RC1RB_0RD0RE_1LD1RE_---0RF_1LA1RF` with E0=halt gives candidate weighted score 9,109, exceeding the existing 7,014 early bound. No timeout is counted as a verdict.

Run `python im-results/agent25-raw123/generate.py` to regenerate the partial proof from the manifest and shared candidate engines. The Lean output imports the original partial audit checker; every certified branch must pass it. The explicit complement is retained in `residuals123`. `Raw123Exact.lean` is a proposed original-source witness and generic quotient graft consumer at target >=9109. The local Lean installation succeeded, but the GitHub checkout failed DNS; **the source audit has not yet passed**. Neither this candidate partition nor its proposed consumer is an accepted theorem or a global BB(6) solution. The next step is to compile the generated source closure and resolve the thirteen leaves.

### Recursive batch checkpoint

Five formerly unresolved tables (4247, 4357, 9109, 11095, 11096) have new induction proofs. Recursive and grammar return lemmas compiled locally against copied exact run0/step0/move0/list definitions. Source transfer wrappers and full weighted consumer still need original-source CI. Decode Raw123RecursiveBatch.lean.zlib.b64 using generate.py, SHA256 ee1b102ca8de7f12201cf4082f1100e968c7d15161c6dd632e38a07ad77e6112. Eight one-hole residuals remain (200 full completions). 4247 uses mutually recursive D/F macros, 11095/11096 a shared strong-induction F return, 4357/9109 triple-token grammar returns. Initial full source check for 13-residual predecessor: run 45598191639. No accepted global closure claimed.

### Phase-aware two-sided finite automata

Four additional residuals have finite BiDFA certificates: 8155 (480 abstract states), 8156 (90), 8174 (506), 8175 (92). Stack summaries combine bounded near-head suffix and length modulo an integer measured since the first 1 from the blank end. Discovered push/pop edges are saturated under the exact Agent16 BiDFA algorithm, independently reproduced with the supplied DFA arrays. Four candidate residuals remain: 573,5465,8146,8209 (100 full tables). Original-source audit is still required. The first CI (45598191639) was interrupted by runner shutdown; completed n-gram modules passed their axiom checks. Isolated new recursive batch audit dispatched at 10:58 UTC.

### Accepted recursive proof and minimized phase certificates

The isolated original-source recursive audit passed: [run 45599941700](https://github.com/FlareZ123/bb6/actions/runs/45599941700), commit 6e10c0c6d8ad916ff6c787e197ac1eebd4e79e12. Thus the five recursive nonhalting theorems above are kernel checked against the repository semantics. No full parent audit has passed yet.

Candidate 573 also closes with a phase counter reset on 001. Greedy congruence minimization leaves DFA sizes and invariant configurations: 573 (9x18,177), 8155 (14x16,113), 8156 (8x9,55), 8174 (14x16,119), 8175 (8x9,57). The exact finite arrays are in spec.json; phase.cpp and minimize_phase.py are untrusted discovery tools. Three explicit one-hole residuals remain: 5465,8146,8209 (75 full completions).