# Raw139 C1=0LA: full weighted cylinder closure

**Result:** all compatible completions of the partial table [7,24,11,24,14,0,3,16,12,11,24,24] have WeightedBound 266. Codes are 4*q+2*w+r, with 24 denoting an unassigned entry. Four holes account for 25^4 = 390625 literal completions. This is normalized residual row (4,0LA), not the global Raw139 parent.

The first-hole partition has 85 split nodes and 1956 terminal nodes: 1251 translated cycles, 546 last-hole cases (maximum queried time 260), 111 FAR witnesses, 47 block-automata witnesses (46 width two, one width three), and one additional translated cycle. The latter is table [7,21,11,13,14,0,3,16,12,11,5,24], entry 2075, period 10, rightward, boundary 39. All terminals close. The initial halt case is charged using the exact first-hole theorem, and all 24 ordinary transitions are covered by certifiedFast and tnf_branch_sound.

## Checked proof and reproduction

Local Lean 4.36.0-rc2 compiled all six block modules, 24 child audit modules and Raw139C1ZeroLACover.lean against the original C1 batch artifact 15083884536 (run 45746968139, source revision 24307ed48c90f18938778cac530c5c3213af2203, ZIP SHA256 b5141e994a4fbbf56d1f226ccd64df425df6d9816b6fcc1282b7ba7e63dea243). Both all_completions_weighted and cover have exactly the standard axioms propext, Classical.choice, Quot.sound. No fresh dependency build is claimed. Raw139C1ZeroLAMatch.lean separately compiled against normalized source artifact 15093190882 (run 45767740664) and proves row membership and exact table equality. The shared object closures differ, so they were deliberately not mixed.

Run python generate.py to regenerate the 31 source files using Agent48's scan and blockcert modules (pinned repository revision 297fb15abe1d39bd2f04df6f4a8a49d2e0d04ffe). The source manifest is SHA256 b579407267b55ad76f2d43e29102e75003127d859e585d1b30c11c04b7b690ea (SHA256 of sorted sha256sum output). The generator asserts the search counts, all 47 block witnesses, and the exact manifest. With the C1 batch object closure in LEAN_PATH, compile the Block*.lean modules first, then Branch*.lean, then Cover.lean; use lean -o MODULE.olean MODULE.lean. The match module requires the normalized closure separately.

The monolithic fastCheck at the root was too expensive to elaborate; composing the individual child proofs solved this. This is a local closure available to the normalized parent consumer after coherent rebuild/integration. It does not by itself discharge all 67 normalized obligations or change the global frontier count.
