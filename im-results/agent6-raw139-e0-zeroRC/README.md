# Raw139 E0=0RC — complete candidate classification, long-query proof

Parent codes `[7,24,11,24,14,24,24,16,9,11,24,24]` (24 is a free slot; ordinary codes are 4*destination+2*write+right). This is the normalized depth-two row (2,0RC), not the distinct D0=0RC row.

## Computational classification
Initial first-query partition: 25,694 splits, 590,963 ordinary leaves, 396,176 translated cycles, 131,349 finite last-hole leaves, 54,205 small FAR certificates, 9,233 open leaves. SHA-256 of the local partition: `77bf4aa9b8c94a9c88204f294b4173028aaeea006f7bd42e2c7e11ac91548665`.
Block-FAR, longer traces and four late-query expansions classify all ordinary leaves: 25,698 splits, 591,055 leaves (396,191 cycles, 131,485 finite last-hole queries, 54,205 FAR, 9,174 block-FAR). All late split halt alternatives are covered by the weighted first-query bound in the proposed assembly. Candidate uniform bound: **1,673,363**, smaller than the common 6,766,859 floor. This is a candidate parent Cover, not a source-accepted parent theorem.

## Proved hard leaf
The one last hard table was `[7,23,11,7,14,1,6,16,9,11,24,19]` (index 5144). The authentic first undefined query is F0 at primitive step 1,673,357. The mathematical recurrence is in `E0ZeroRCRecurrence.lean`; local Lean 4.36.0-rc2 checked `BB6.Agent6E0ZeroRCRecurrence.first_query` and `weighted : Cover (WeightedBound 1673363) p`. Axiom set is standard (propext, Classical.choice, Quot.sound). The local check used the existing accepted canonical77 artifact's PartialAudit dependency closure. An independent source-closure CI audit is desirable for promotion.

The B/C inner loop maps a B configuration with three leading ones, j repeated 0111 blocks, and final 01 to a B configuration with one leading one and right run length n+6(j+1). Its exact cost is (j+1)(4n+16+12j). Eleven outer phases start at step 76 and reach F0 at step 1,673,357. The proof is symbolic in the inner repetition count, with finite short bridge equalities. It avoids the earlier 3,255-action packed trace approach (`tracegen.py`, exploratory; monolithic packed checking exceeded local memory).

`Hybrid.lean` adds a general verified certificate constructor that composes bounded Covers with ordinary FastThreeHoleAudit leaves and checked first-query splits. Its soundness theorem and generic fromCodes no-assigned-halt lemma passed local Lean. This enables exact parent assembly using the hard leaf without replaying its 1.67m primitive steps.

`reproduce.py` preserves the deterministic search and recipe reconstruction; it is an untrusted generator and the independently checked proofs are the boundary of mathematical acceptance. No BB(6) universal upper bound or global roster reduction is claimed here.

## Exact remaining proof cut

Run 45827711630 published 20 of 24 exact root Covers. The four missing roots 00, 07, 12, 18 were repacked into 63 independent top-level child cuts without changing their 5,919 original declarations. Run 45906701973 accepted 13 of 16 cut groups. Run 45916648450 then accepted eight of twelve additional subparts; **only 08/0, 10/0, 10/2 and 13/0 remain**. Each failed with a runner shutdown (exit 143), not a reported Lean theorem rejection. The parent theorem remains unaccepted.

The next exact recovery mode (recovery_run_id=45916648450) uses [resume.py](resume.py) to pool the already accepted source/object identities, assert the exact missing top-level child list, and rewrite only unaccepted batch modules. It isolates each old declaration in a new module and replaces nested closed audit splits by independent exact-table child Covers. The leaf evidence, ordinary move order, bound and original parent theorem remain unchanged; the new child Covers and joins are independently kernel checked by Hybrid.sound. This is a proposed speed/memory repair, not yet an accepted proof. It avoids recomputing any accepted cut or re-enumerating the 591,055 candidate leaves. Timeout recovery exports only quarantined dependency-closed partial objects; the parent consumer runs only after every missing exact child passes.
