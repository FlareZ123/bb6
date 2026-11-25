# Raw124 subcylinder work, 2026-11-25

Raw124 = `1RB---_1RC---_0RD---_1LD1RE_---1LF_------`. First new query F1 at 7 moves. Each fixed ordinary F1 row has 25^5 = 9,765,625 raw completions; the weighted checker handles early halts and initial blank delay.

## Completed candidate branches

| F1 | Proposed weighted bound | Previously open leaves | FAR | Inductive | Late halts | Outstanding |
|---|---:|---:|---:|---:|---:|---:|
| 0RF | 71 | 42 | 42 | 0 | 0 | 0 |
| 0LC | 145 | 282 | 280 | 2 | 0 | 0 |
| 1RF | 140 | 1171 | 1160 | 11 | 0 | 0 |
| 0RB | 272 | 570 | 560 | 10 | 0 | 0 |
| 0RD | 267 | 143 | 141 | 2 | 0 | 0 |
| 1LC | 102 | 243 | 242 | 1 | 0 | 0 |
| 1RD | 80 | 861 | 859 | 2 | 0 | 0 |
| 0RC | 2759 | 374 | 362 | 11 | 1 | 0 |
| 1RC | 688 | 799 | 794 | 5 | 0 | 0 |
| 1LD | 7 | 0 | 0 | 0 | 0 | 0 |
| 1RE | 7 | 0 | 0 | 0 | 0 | 0 |
| 0RA | 283 | 656 | 633 | 23 | 0 | 0 |

These are exhaustive candidate audits, not accepted source-level proofs. Together they represent 117,187,500 raw completions. The 0RC delayed last-hole encounter at step 2753 required increasing the proposed bound from 240 to 2759; the 1000-step exploration cutoff is never itself proof of divergence.

## Reproduction

Original four branches: generate_rf.py, generate_lc.py, generate_1rf.py, generate_0rb.py. Other eight: generate_bundle.py and compressed JSON witness bundles complete-bundle*.json.zlib.b64, including hashes of deterministic open leaf lists and trees, FAR automata, and symbolic operations. The generators produce source Lean Audit trees with explicit finite proof checks, partitioned to bound reduction cost. Run manual agent13-coverage target weighted-tnf-raw124-rf/lc/1rf/0rb/bundle. No dispatch capability in this session. Direct git clone DNS unavailable.

Agent2MultiPump.lean extends Agent50's open-tail transfer lemmas to arbitrary finitely many repeated blocks, each with an independently quantified repetition count. A finite operation list proves an existential exact runtime and positive lower bound for every parameter environment. Its ordinary growth certificate uses all repetition counts n simultaneously. Agent2Nested.lean uses three independently quantified variables to certify nested counter loops for 1RF leaves 341 and 923. Local Lean 4.36.0-rc2 checked the general operational theorem, the eight initially collected multiblock certificates, both nested counter proofs, and all 21 single/multi witnesses in the seven-branch bundle against a reconstruction of the source executable tape semantics. Source integration adapters to NeverHalts and full source-level tree acceptance remain pending CI. No sorry or native_decide in the committed proof sources.

## Discovery improvements

0RB index 238 (zero-based in deterministic open.txt), `1RB0LF_1RC1LA_0RD0RF_1LD1RE_---1LF_0LA0RB`, had resisted exhaustive six-state DFA enumeration. A 32-state last-five-bit suffix DFA certified it, and congruence quotienting reduced it to nine states. It is now included in generate_0rb.py. Pooling successful DFAs across sibling branches yielded over a thousand new certificates. Enumeration and FAR search reused raw99/enumerate.cpp and agent11-tnf-raw86/search.cpp.

Automatic multiblock candidate inference uses four tape snapshots with constant growth increments, dynamic programming to segment into constant and repeated words, and finite symbolic search for exact sweep/rewrite operations. Proof checks do not trust the search. A complete proof of raw124 is not yet claimed.


## F1=0LB — recursive source audit in progress

The first 3,691-cycle / 508-hole scan was retracted: `enumerate.cpp` emits underscore-separated display tables, whereas `longcycle.cpp` indexes compact 36-character transition strings. The earlier scan passed display underscores through unchanged and its counts/certificates are invalid.

The corrected `generate_bundle.py` strips underscores before every C++ query and recursively resolves multi-hole hits: each such leaf becomes a 24-way `Audit.split`; translated cycles become `Audit.cycle`, and only genuine one-hole leaves become `Audit.last`. Open leaves are deferred until all descendants at the current cap are processed, then retried at a larger cap. Independent C++ batches now run in two processes.

Current CI run: 45615959400 (`raw124_bundle_prepare` job 139211302469), dispatched with a 60-minute prepare timeout and serial Lean shard compilation. The generated bound is asserted to be at most 2,000,000. No 0LB classification or source-level `bound_all` theorem has yet been accepted. Once available, `Raw124ChampionBound.branch_bound_le_champion` provides the numeric lift to the champion score, followed by `weightedBound_mono_local` for roster integration.
