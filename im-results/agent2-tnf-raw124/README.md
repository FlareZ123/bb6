# Raw124 subcylinder work, 2026-11-25

Raw124 = `1RB---_1RC---_0RD---_1LD1RE_---1LF_------`. First new query F1 at 7 moves. Each fixed ordinary F1 row has 25^5 = 9,765,625 raw completions; the weighted checker handles early halts and initial blank delay.

| F1 | Proposed weighted bound | Cycle leaves | Last-hole leaves | FAR leaves | Inductive leaves | Outstanding |
|---|---:|---:|---:|---:|---:|---:|
| 0RF | 71 | 6979 | 1260 | 42 | 0 | 0 |
| 0LC | 145 | 26097 | 5270 | 280 | 2 | 0 |
| 1RF | 140 | 12897 | 2608 | 1160 | 11 | 0 |
| 0RB | 272 | 32488 | 7216 | 559 | 10 | 1 |

Counts are candidate enumeration results, not accepted source-level certificates yet. All complete branches have generators: generate_rf.py, generate_lc.py, generate_1rf.py. These emit explicit Lean Audit trees and require checked concrete leaves; simulation cutoff is never a proof. Run manual agent13-coverage target weighted-tnf-raw124-rf/lc/1rf. No dispatch capability in this session. Direct git clone DNS unavailable.

Agent2MultiPump.lean extends Agent50's open-tail transfer lemmas to any finite number of repeated blocks, each with an independently quantified repetition count. A finite operation list proves an existential exact runtime and positive lower bound for every parameter environment. Its ordinary growth certificate uses all repetition counts n simultaneously. Local Lean 4.36.0-rc2 checked the general operational theorem and the four concrete multiblock certificates in multi-witnesses.txt against a reconstruction of the source executable tape semantics. Agent2Nested.lean uses three independently quantified variables to certify nested counter loops for 1RF leaves 341 and 923, with local kernel validation of every transition and the arbitrary-runtime theorem. Integration adapters to NeverHalts and the full source-level tree remain pending CI. No sorry or native_decide.

0RB unresolved index 238 (zero-based in deterministic open.txt): `1RB0LF_1RC1LA_0RD0RF_1LD1RE_---1LF_0LA0RB`. At A with blank current and empty left, it repeatedly rewrites runs 0^a 1^b (b=3 or 6); may admit an inductive prefix-transducer invariant. Other 0RB witnesses in single-witnesses.txt, multi-witnesses.txt. Open.txt hash ec5a42680c391cef5c2184ec403c1fa92310b8d1dec3f3bdf2384164274997ae. Enumeration and FAR search reused raw99/enumerate.cpp and agent11-tnf-raw86/search.cpp. Do not treat the unresolved branch or the full raw124 parent as closed.
