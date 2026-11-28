# Raw44 audit reduction and top-level progress

Local Lean 4.36.0-rc2, using the exact checker sources and compiled dependencies from accepted GitHub artifact 15220979453, kernel-checked:

* `Raw44FastZipCheck.lean`: extensional equality of the accelerated check and the original zipCheck (standard axioms only). The finite incoming-delay set is contained in 0..5, so the weighted check can use an immediate sufficient inequality; otherwise it uses the original checker. This follows Agent32's Raw59QuickWeight.
* `shard_audits.py`: untrusted structural emitter; each small subtree is checked by the equivalent fast check, and each larger split is joined by a proof for all 24 ordinary outcomes. The first 2641-node C1=1LE subdivision passed in 32 seconds with peak RSS 2.46 GB. Full 1LE/1RE audits are still running; this does not claim their final cover.
* `Raw44B1RCJoinCore.lean`: genuine C1-halt branch weighted bound 10 (seven ordinary steps plus the halt and at most two incoming blank steps). The conditional join explicitly requires all 24 ordinary child proofs.
* `Raw44Top.lean`: from the original seven-hole Raw44 parent, B1 is first queried after six ordinary steps. Its genuine halt branch has weighted bound 9. Five ordinary B1 outcomes are proved never to halt for every compatible completion: 1RB, 0LC, 0LD, 1LD, 1RD. All five and the halt theorem have only propext, Classical.choice, Quot.sound. These are six disjoint physical cylinders of size 25^6 each, 24% of the original Raw44 cylinder. No exact overall BB(6) value or global canonical-roster decrement is claimed.

Each result is source-checkable. The local direct GitHub clone failed DNS; the connector was used to push source, and accepted artifact objects supplied dependencies. 
