# Raw139 normalized D1=0RD (agent6)

New depth-0 row (0, code 13): [7,24,11,24,14,24,24,13,24,24,24,24], ordinary code 4*destination+2*write+right, unknown 24. Not yet a closed row or global roster removal.

**Lean**: D1ZeroRD.lean compiled locally with Lean 4.36.0-rc2 against the accepted normalized artifact 15093190882. exactTable and rowMember link to Raw139Normalized; cover uses the real first-hole TNF theorem, 11 checked side cycles, and the weighted halt branch at t=5 (bound 11). Remaining D0 codes 2,6,8,9,10,16,17,18,19. Axioms: propext, Classical.choice, Quot.sound. No fresh dependency rebuild claimed.

## Candidate census, cutoff 250

| D0 | Leaves | Unclassified |
|---|---:|---:|
|2|3083389|19211|
|6|2521662|7244|
|8|1476367|7371|
|9|1115867|3863|
|10|2440873|24267|
|16|3754820|36142|
|17|3266852|29336|
|18|8031302|56348|
|19|5898765|23277|

All partition identities checked by arity-aware counts. Prefix-sharing census with exact translated cycles, small FAR, state graph closure and last-hole leaves; untrusted discovery, not Lean proof. Compressed sources reconstruct with Python standard library: lzma.decompress(base64.b64decode(Path(...).read_text())). Compile g++ -O3 -std=c++17. Run d1 D0 250, which writes /tmp/d1-0rd-d0-D0-cap250.txt. Run strong input 1 then run stage 2 on stage-1 open lines converted to '250 TABLE'. Strong adapts Agent47/32 sparse ngram and Agent48 block FAR; adds exact-replayed hash-assisted cycle candidate search. Candidate holdouts include both late queries (must expand multi-hole cases) and unclassified machines.

D0=8 and 9 have zero stage-2 open leaves. All their late replay leaves (85 exact tables: 48 hole cases and 37 translated cycles) now have a kernel-checked weighted Cover at B=3000. Only one late hole has more than one unassigned slot, and its full 24 ordinary children plus the halt branch are checked. The abstract ngram/block and earlier census leaves still require parent integration.

## D0=8 and D0=9: complete late-replay cut

[D1EightReduce.lean](D1EightReduce.lean) now kernel-checks the exact D0=8 first-C1 reduction. For
`[7,24,11,24,14,24,8,13,24,24,24,24]`, blank execution reaches the open C1 slot at
ordinary step 8. Twelve of the 20 TNF-admissible ordinary C1 codes are discharged by exact
translated-cycle audits; only codes `[1,2,3,6,16,17,18,19]` remain as child-Cover
hypotheses. Thus `BB6.Agent6D1EightReduce.cover` proves the complete D0=8 cylinder at
every weighted bound `B ≥ 14` from exactly those eight child Covers. Local Lean
4.36.0-rc2 checked the theorem against accepted normalized artifact 15093190882 with only
`propext`, `Classical.choice`, and `Quot.sound`. The cap-250 replay census partitions
the eight hard children into 1,476,355 terminal leaves plus the twelve immediate cycles
(1,476,367 leaves total) and 7,371 cap-250 open leaves; those counts are discovery data,
while the eight-child reduction itself is a kernel theorem.

[D1NineReduce.lean](D1NineReduce.lean) supplies the parallel exact D0=9 composition interface.
For `[7,24,11,24,14,24,9,13,24,24,24,24]`, the same step-8 C1 split has only
six hard ordinary codes, `[2,6,16,17,18,19]`; the other 14 children are
kernel-checked translated cycles. `BB6.Agent6D1NineReduce.cover` proves the complete
D0=9 cylinder at every `B ≥ 14` from those six child Covers. Local Lean
4.36.0-rc2 accepted it with only the standard axioms. The source gate in
`.github/workflows/agent6-raw139-d9.yml` is independently rebuilding all six child
certificate banks and their unconditional weighted-3000 parent composition.

The exact certificate bank is reproducible from [late-source.tar.xz.b64](late-source.tar.xz.b64), containing the untrusted generator and two fixed witness manifests. Extract with `base64 -d late-source.tar.xz.b64 | tar -xJf -`. In the accepted normalized artifact 15093190882 build directory, run `python certify_late.py --roots lateRoots.tsv --children lateChildren.tsv`, then `LEAN_PATH=. lean -o D1Late.olean D1Late.lean`. The generated module SHA-256 is 138dfdbc02d63f28ac39d44d9ec19f7d2baecfaab646be83990f0c40b3c05cf3. Local Lean 4.36.0-rc2 checked `BB6.Agent6D1Late.allLate` with only propext, Classical.choice, Quot.sound. The `tables` list is an exact list of the 85 partial-machine roots, not a statement about the complete census partition.

The formerly multi-hole table [7,24,11,24,14,16,8,13,20,1,23,3] first queries B1 at 295 ordinary moves. Its 24 ordinary children partition into four last-hole arrivals at 296 or 297, six translated cycles, and 14 ngram certificates (13 width-2 and one width-5). The exact source `zipCheck` checks the split, every child's table identity, the weighted halt allowance, and the leaf certificate. It needs no remaining hypotheses. Ngram certificates use a compact trie constructor from sorted row keys, with every closure equality reduced by the kernel. No new axiom or trusted discovery algorithm.

The late D0=8 set is 28 hole cases (including this two-hole parent) and 16 cycles; D0=9 has 20 last-hole cases and 21 cycles. The maximum checked arrival is 2782. The unresolved proof edge is full census certificate transport: 4225 ngram and 3102 block candidates for D0=8; 1688 ngram and 2134 block candidates for D0=9, besides the original 250-step census leaves. No parent or global roster cut claimed.

 The sole D0=6 stage-2 open leaf is solved below; D0=2 has source-checked Covers for all eleven former stage-2 open leaves. No complete branch bound is certified.

## D0=2: all eleven source-checked hard-leaf Covers

The two-stage census is now preserved by exact table code in [D0TwoHoldouts.tsv](D0TwoHoldouts.tsv). Stage 1: 11,088 ngram, 6,855 block, 405 cycle, 507 first-hole and 356 open candidates (19,211 total). Stage 2 on those 356: 120 ngram, 209 block, 16 first-hole and eleven open. All eleven now have kernel-checked Covers: six nonhalting proofs and five finite weighted Covers. ID3 reaches the sole missing F1 slot after exactly 795,108 ordinary moves, giving bound 795,109; ID27 is resolved by an all-time reset invariant below. The stage-1 and stage-2 finite classifications are not yet collectively certified.

* [D1NestedGrowth.lean](D1NestedGrowth.lean), theorem `BB6.Agent6D1NestedGrowth.two_cover`: ID209 shares the exact nested pair-of-zero recursion with the prior D0=6 hard leaf despite different internal state routes. From blank after eight steps, the E family has left stack `0^(2k+2)101` and empty right stack; arbitrary-tail DP/EP macros prove growth for all k by induction on k+j then k.
* [D1TwoUnary.lean](D1TwoUnary.lean), theorems `cover354` and `cover355`: both tables enter the B family after seven steps with left stack `1^(4k+2)01` and empty right stack. A shared recursion grows the left run by four ones; the general four-zero consuming macro uses two lower-index recursive sweeps. Exact terminal blank return and positive growth are proved independently of any empirical pattern extrapolation.

* [D1TwoLatePair.lean](D1TwoLatePair.lean), theorems `cover6` and `cover7`: the same unary/block return law applies to two distinct transition tables. Each `011` block is consumed, adding five unary symbols. At an all-unary section of length n=3k+a, the sweep leaves a unconsumed ones; residue a=2 reaches the sole missing E0 transition, while a=0,1 return to unary/block sections. The exact blank-connected all-unary sequence is 9,22,49,94,169,294,497. Lean proves first query after 78,752 and 77,850 live steps, respectively, and the weighted bounds 78,753 and 77,851, for all completions. This is a finite-arrival classification, not an infinite-growth proof.

* [D1TwoLate163.lean](D1TwoLate163.lean), theorem `cover`: exact first query of F0 at step 21,697, using 44 independently checked zipper segments and their composition; weighted bound 21,698.

These three nonhalting examples quantify over every compatible completion and arbitrary weighted bound B; the three finite-arrival examples use the indicated concrete bounds. They compiled locally with Lean 4.36.0-rc2 against the existing accepted Raw139 normalized artifact 15093190882, with only propext, Classical.choice and Quot.sound. No full parent closure, fresh dependency build, or global roster cut is claimed.


### ID3: exact final hard-leaf Cover by a reusable local-rule dictionary

For `[7,19,11,0,14,23,2,13,9,16,5,24]`, the generated theorem `A6ID3.readArrival` proves `(knownRun p 795108).map readSlot = some (5,true)`; `A6ID3.cover : Cover (WeightedBound 795109) p` closes every compatible completion via the source last-hole certificate. Both exported theorems compiled locally in Lean 4.36.0-rc2 against accepted artifact 15093190882, with only propext, Classical.choice, Quot.sound. The 407 distinct local rules cover 49,695 ordered applications (49,694 of length 16 and one of length 4). All 50 replay shards and the final consumer compiled. This is the last of the eleven hard leaves, not the whole D0=2 parent.

[A6BitTrace.lean](A6BitTrace.lean) uses length-free binary naturals for the two zero-padded tape halves, proving exact commutation with the original projected run and transport to knownRun. [A6WindowMacro.lean](A6WindowMacro.lean) checks a finite window with explicit left/right lengths and proves arbitrary-tail extension via division and remainder by two. Each Rule carries its own kernel proof of the strict finite-window run. The replay checks only matching prefixes and reattaches untouched quotient tails; the local proof is shared by every occurrence. Unlike repeated-block sweep replay, a local rule may execute an arbitrary finite mixed-direction word. This exploits recurrent short windows even when the large tape does not exhibit repeated homogeneous sweeps.

Copy the two Lean files and [genID3.py](genID3.py) into the extracted normalized artifact's build directory, set LEAN_PATH to that directory, compile A6BitTrace and A6WindowMacro to .olean, then run:

    python3 genID3.py > modules-id3.txt
    while read -r m; do lean -o "$m.olean" "$m.lean" || exit 1; done < modules-id3.txt

The deterministic Python generator is untrusted: every rule and replay equality is checked using rfl, and eval_reach joins the exact primitive-step costs. Local blob SHA-1s of the compiled inputs are 1f35fdcf1041cfbf650134a323d6a0d51af85002, 5fe466b4b376e6d0c200b07e75bf387ae6ceb2d6, and 3a0fdd6dd0d1a8da581c71ca60f83e2fba58fcdb respectively. No fresh upstream dependency rebuild or canonical roster reduction is claimed.

## Exact symbolic closure of D0=1LB hard two-hole leaf

D1SixGrowth.lean proves all completions of [7,24,11,24,14,17,6,13,9,22,20,12] nonhalting (A1 and B1 are arbitrary). It is the only stage-2 unclassified leaf in the D0=6 branch before late-child expansions. It proves two parameterized local return maps with arbitrary untouched tails, using pairs of zeros z(k)=0^(2k). E(k) fills the adjacent right zero with one, without changing its left stack. D(k,j) transfers a zero pair from the right to the left between two one-markers, changing control D→E. The nested induction on k+j and k is essential: D(k+1,j) uses E(i) for i≤j, E(k), and D(k,j+1). The latter preserves the sum and reduces k; all E calls reduce the sum. From blank after 8 moves, E has left stack z(1)101, right empty; positive return maps increase k forever. The exact theorem BB6.Agent6D1SixGrowth.cover is valid for arbitrary B. All source compiled locally, standard axioms only.

TNFGraph.lean supplies a source-proved closed-state subset leaf. NormalizedPrefixAudit.lean combines graph closure, exact imported covers, existing zipper prefix sharing, and normalized first-query branching. It extends the existing approaches (in particular Agent32's packed normalized prefix checker) with these leaf forms; no independent novelty claimed for normalization or prefix sharing. Its sound theorem is locally kernel accepted, with only the standard axioms. These are integration tools, not full parent closure.

## Checked sweep replay and new side-cycle candidates

[CheckedSweepTrace.lean](CheckedSweepTrace.lean) verifies strict finite windows (no read outside either explicit frame), lifts one-window steps through arbitrary untouched tails, checks sweep actions, and composes their exact costs in `eval_sound`. [PackedSweepTrace.lean](PackedSweepTrace.lean) represents lists by their length and little-endian binary natural; it proves packed prefix removal, logarithmic repetition and exact equivalence to the list evaluator, including `reach_extend` and `reach_read` in the original known-run semantics. Both compiled locally on Lean 4.36.0-rc2 against artifact 15093190882; standard axioms only. This infrastructure is exact proof checking. A6Trace335.cover is now kernel checked (first query F0 at 64,089; weighted bound 64,090).

## Source-checked translated cycles (77,78)

OneSideSweep.lean proves strict one-sided replay with arbitrary older left tail and positive growth. D1TwoCycles.lean proves both covers (any weighted bound). Blank entry 32835/30903 and period 16333/15373, respectively; common 64-cell retained prefix W, common 107-cell inserted word V, and common 189-cell older tail T. The exact period equality is `forall L, run0 p period ⟨3,W++L,[]⟩ = some ⟨3,W++V++L,[]⟩`. This gives an unbounded sequence of live returns, not an inference from long simulation. All compiled locally on Lean 4.36.0-rc2, accepted artifact 15093190882; axioms propext, Classical.choice, Quot.sound. No full parent cover.

Reproduce generated source modules: `python discover.py 335 77 78` then `LEAN_OUT=PATH python genshard.py 335 77 78 > modules.txt`. Build CheckedSweepTrace, PackedSweepTrace, OneSideSweep against the normalized artifact, then compile each module in modules.txt in order (`lean -j2 -o MODULE.olean MODULE.lean`), then D1TwoCycles. The generated data and shards are independently checked by Lean, with rfl in each exact action-list evaluation. Monolithic replay exceeded memory; splitting into 500-action modules (25 actions per declaration) succeeded. ID27 previously reached 1e9 live steps without a hole (75,134-cell span); the all-time proof below supersedes that simulation.

## ID27: complete all-time counter/reset nonhalting proof

Exact codes `[7,16,11,9,14,1,2,13,20,24,8,15]`. [D1TwentySeven.lean](D1TwentySeven.lean) proves `BB6.Agent6D1TwentySeven.cover (B : Nat)` for every weighted bound and every compatible completion. Local Lean 4.36.0-rc2 checked the exact source against accepted original-source compiled artifact 15093190882; `cover` depends only on propext, Classical.choice, Quot.sound. `blank_seed` and `nextGood` depend only on propext and Quot.sound. No fresh dependency rebuild or canonical parent cut is claimed.

The projected zipper stores its scanned cell at the front of the left list. Put P=001010001000100100101001, W=0010000100010, V=010, U=1001. Let S(x,n,L) be state C, left list P W^(x+1) V^(2n) 000 L, right list empty. The authentic blank orbit reaches S(0,15,L0) after exactly 13,178 live steps, with L0=100001010011001100110011000000100011001. The invariant Good comprises S(0,n,L) for every n>=2 and arbitrary L. The ordinary return S(x,n+1,L) -> S(x+1,n,U L) costs 124x+48n+519. Iterating gives S(n,0,U^n L), leaving at least two U blocks available for the reset. The first boundary sweep and transfer phase consume all W blocks, growing an archive of 0011 blocks. For starting n>=2 their exact endpoint is state C, left list P (001)^(3n+6) 00001 (0011)^(n+1) 0001 U^(n-1) L, right list empty. The parity split is complete: if 3n+6=2x+6, resetEven returns to S(0,x+2,100101 T) for arbitrary archive T; if 3n+6=2x+7, resetOdd1 and resetOdd2 use the first three archive blocks (available since n>=2) and return to S(0,x+6,10000101 T') for the remaining tail T'. Both returns have positive cost and preserve Good. Unbounded live prefixes then imply NeverHalts for all compatible completions. All nine local exact macro identities, arbitrary-tail transfers, drain, parity case split, positive return, and blank seed are kernel checked.
