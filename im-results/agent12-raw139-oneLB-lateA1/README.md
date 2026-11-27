# Raw139 C1=0LB long A1 queries: certified accelerated return map

Two exact one-hole tables from Agent 3's residual roster:
- false: [7,24,11,22,14,9,17,16,6,11,16,0], c=9,index=212,v=0. First A1 query after 125150404 ordinary moves. Weighted bound 125150410.
- true: [7,24,11,22,14,9,17,16,6,11,15,0], c=9,index=218,v=0. First A1 query after 187672020 ordinary moves. Weighted bound 187672026.

The return map is Agent 3's discovery (../agent3-raw139-e0-oneLB/long-returns.md). This dossier supplies the Lean kernel proof. At a C frontier, scan token runs a=010 and b=1 leftward through E. Replace the tokens with buffers 110 and 1, respectively; after the delimiter, C sweeps back, outputting 100 and 0 in the left ray. All local rules are proved definitionally over arbitrary infinite rays, and run repetitions proved by induction. Packed Nat prefix guards connect the large integers to the exact tape rays. The Python generator only proposes checked runs. The 7656 successful returns and final query are verified in 256-return blocks, with 20390 run-length certificates. No reliance on native_decide, simulation trust, or an external prover.

## Reproduce

Use Lean 4.36.0-rc2 and the accepted original-source build closure (e.g. Agent 3 artifact 15169732599, run 45934344615). Put these source modules plus ../agent12-raw139-oneLB-c1-286/Counter286.lean and Counter286Bridge.lean into a directory on LEAN_PATH, with the original build path. Compile Counter286, Counter286Bridge, LateCert; run:

    python gen_a1.py LateA1Checked.lean
    lean -o LateA1Checked.olean LateA1Checked.lean

Local end-to-end compile of the generated 315 KiB certificate took 16.34 seconds and 2427240 KiB peak RSS. Exact checked source blobs LateCert.lean 9f2a1254ba18154518844ed5149260bad7ff3995 and gen_a1.py a00a5e00075f00db8e2af6482550d416e78b6af8. Standard axioms only: exact_query [propext, Quot.sound]; weighted [propext, Classical.choice, Quot.sound].

## Consumer

BB6.Agent12LateA1.ctr false/true is the exact table; BB6.Agent12LateA1.weighted v B hb : ∀ m, compatible (ctr v) m → WeightedBound B m, where hb : choose v 125150404 187672020 + 6 ≤ B. For the WeightedAudit graft, replace the corresponding long replay module's all_completions_weighted proof with this theorem and the exact variant. Its proof uses the original BB6Coverage.run via the checked observe_move bridge; if the unassigned A1 is a move then all 12 transitions are moves and the completion cannot halt, otherwise it halts at the exact query. The five-step maximum leading blank delay gives the weighted bound.

This is local original-semantics verification over an accepted dependency closure; the parent is not yet claimed integrated. No new CI or source closure rebuilding needed before the parent graft.
