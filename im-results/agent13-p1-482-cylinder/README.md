# P1: candidate full blank-root exclusion at n = 482 (mod 4096)

Agent 13, 2026-11-05. **Research intermediate.** This adapts Agent 8's original-source checked 26-node parametric P1 inverse cone to a distinct, smaller 22-node affine graph. The source is included for review and manual CI checking; no assertion of BB(6) completion.

Let q=30+256r (r≥0), n=16q+2=482+4096r, and u=7·2^(16q)−4q−3. The candidate theorem `BB6.Agent13P130.critical_482_mod4096_unreachable` excludes the original blank-root critical target `Reach 2 (14·2^n−2n−10)` for every such n. The proof reduces the target to Agent45's two authentic feeder roots and uses a finite affine shadow closure, a uniform bound of 10 on accumulated odd inverse cost, a source-complete G inverse, source even-hub power obstruction, a c=1 source exception obstruction, and a well-founded 11−m inverse proof tree.

## Exact new affine certificate

On the L0 feeder, the initial shadow node is (0,364+3072r), with 13 affine nodes. L1 starts at (0,304+2560r), with nine nodes. Every node is displayed in `P130Arithmetic.lean`; its exact shadow edge is z=2^t v, 2z'+1=16q+s+m+t+v, s=8 or 9, and its new node is (m+t+1,z'). All 22 node forms avoid divisibility by 256 for all r≥0. The cumulative m coordinate is at most nine, with t at most eight; exact machine acceleration uses unchanged Agent1/9/45/47/50 source imports.

The finite parametric graph was independently checked in Python at r=0,1,2 and the source-generated Lean proof at this commit is the proposed definitive certificate. **Check the manual workflow outcome and final Lean axiom audit before describing this result as original-source certified.** The new index class is disjoint from Agent8's n≡466(mod16384) sector. It strengthens Agent12's earlier n≡482(mod65536) subset if the authentic proof checks. Other index classes and the machine's final halting behavior remain unresolved.

## Proof files and provenance

Ten Lean modules `P130Arithmetic`, `P130Source`, `P130Depth`, `P130Power`, `P130Width`, `P130Exception`, `P130NoEven`, `P130Blocked`, `P130Root`, `P130Final` mirror the existing successful original-source Agent8 cylinder proof strategy, while replacing the base q29+1024r with q30+256r and the original affine graph with the independently computed 22-node graph. Adapted statements must be checked by the full workflow `.github/workflows/agent13-p1-482-source.yml`. This is a proof attempt until that succeeds. External novelty has not been assessed.
