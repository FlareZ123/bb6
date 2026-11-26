# Raw139 E0=0RA candidate closure and checked packed audit

Exact proposed normalized cylinder: [7,24,11,24,14,24,24,16,1,11,24,24], codes 4*q+2*w+r, 24 unknown. Six holes = 244140625 literal completions. First unknown query B1 at time 9. Full 24 ordinary branches, no state quotient.

C++ bounded census (250 steps, cycle period <=120, 1/2-state FAR): 557737 nodes including root, 23239 internal splits, 534498 terminals. Terminal counts: 402941 translated cycles, 103456 last-hole queries, 24549 FAR, 3552 open. Python classification gives 1883 block invariants (some reflected), 1601 FAR, 59 cycles, nine late queries. Only one late query has multiple holes: [7,24,11,22,14,17,24,16,1,11,3,20], A1 at 4808. All 24 ordinary children classified (17 FAR, seven last queries at 4809/4810); halt child charged separately. Proposed common weighted bound 321796, based on exact last-hole query 321790 of [7,2,11,19,14,20,13,16,1,11,24,10] at F0. No open candidate terminal.

**Source-checked full six-hole Cover accepted in CI run 45778885358.** All 24 ordinary B1 branch Covers compiled (17 child jobs, with the eight easy codes grouped in one job), followed by the parent theorem BB6.Agent3E0RA.cover and BB6.Agent3E0RA.all_completions_weighted. The parent proof has only [propext, Classical.choice, Quot.sound]. The exact normalized row match is recorded in Raw139E0ZeroRAMatch.lean; Raw139E0ZeroRAIntegrated.lean removes that row from the 67-row residual list of the historical Canonical77 snapshot and exposes a 66-row parent wrapper. The active Canonical68 programme in im-results/agent6-champion-residual/README.md has a different 85-row residual interface; no transport from this 77-way row to that current consumer is claimed. That source-level integration is being compiled in CI run 45790610736. Until it passes, this is a certified local-cylinder Cover, not a global Raw139 completion; do not claim a Canonical64 frontier-count change.

## Checked reusable result

Agent3PackedAudit.lean inside source.tar.xz is kernel checked in Lean 4.36.0-rc2, SHA256 9209161803c20545ee295076a523f703c3896294458c939e2b5104bb702c3761. It imports ZipAuditCore and FastThreeHoleAudit, defines packed tape execution, proves packed_read, pcycle_sound, pquery_sound, and PAudit/pcheck_sound (allows exact-table-matched already checked semantic bounds at leaves). Axioms: packed_read and pcycle_sound [propext, Quot.sound]; pcheck_sound [propext, Classical.choice, Quot.sound].

The longest trace and its leaf cover also compiled successfully: BB6.Agent3E0RALong.trace and .cover, standard axioms. 315 segments (1024 moves except final remainder), 20 Part modules, 20 explicitly indexed Join modules, one final Cover. The original monolithic pjoin composition OOMed. Explicit indices and group theorems eliminate giant definitional reduction. Exact final packed state q=5, head=32, left=2124551971267068394758352826209874509318372470908127692797776552801614239443408970956650009060917142675557317944986004061386317350610828957638079915066349407775325083341572876126912510, right=2.

## Reproduction

Extract source.tar.xz in this directory (SHA256 fb2d8506761f3a7843e59d16202ad069f68fba835dca9e5b03fe46623dd58b7d). Generator scripts use existing Agent48 scan.py/blockcert.py and the Agent3 C1 emitter; all Python generators are untrusted. C++ census adapted from Agent6.

g++ -O3 -std=c++17 census.cpp -o census
./census 1 > counts1.txt
python classify.py
# hard.jsonl, latechildren.json, latehard.jsonl bundled from successful search; hard.py regenerates hard.jsonl
python long.py
python emit_family.py 11 18 8 # or all integer B1 codes 0..23

CI run 45778885358 completed the full 24-child family and parent composition. Its raw139-e0-0ra-certified artifact (ID 15100202529, SHA256 digest c8863774ecc4349623b087800cd45cf977add303ea4b3c1920e130b0571b2b42) contains A3E0RACover.lean, its kernel-checked .olean, and the parent log. The exact normalized membership/equality module is Raw139E0ZeroRAMatch.lean. Raw139E0ZeroRAIntegrated.lean turns that match into a 66-table residual interface for the historical Canonical77 snapshot; CI run 45790610736 is rebuilding that accepted closure and checking this integration. This is not yet connected to the active Canonical68 85-row consumer. A separate Raw139E0Canonical68Probe.lean now tests whether the same six-hole table appears among the active 80 descendants after the 43-sibling refinement; it is included in the next Agent6 workflow run. Until that membership proof passes, no subtraction from the active 80 is claimed.

Set A3_BUILD to the target build directory or use default generated/. Compile Agent3PackedAudit.lean into the build directory first. Use original C1 batch artifact 15083884536 (run 45746968139, source revision 24307ed48c90f18938778cac530c5c3213af2203, ZIP SHA256 b5141e994a4fbbf56d1f226ccd64df425df6d9816b6fcc1282b7ba7e63dea243). Compile original SparseZipper, SweepPumping and ZipAuditCore sources (available in normalized artifact 15093190882, run 45767740664) against that coherent closure, not the separately built objects. Compile A3E0RALongBase, all Part, all Join, Cover. Then compile modules in modules{b}.json order. B1=11 generator tested: 929 splits, 39 initial open leaves, 5 block shards, 104 small audit chunks, max 385 nodes. The full 24-child family and parent Cover are now kernel-checked in CI. Python partition checks remain witness-generation aids only; mathematical acceptance is Lean checking of generated statements. The normalized row equality is source-level in Raw139E0ZeroRAMatch.lean; the combined 66-row wrapper is under CI validation. This is an intermediate cylinder result, not a complete BB(6) upper bound.

Long cover generator uses actual trace endpoint and independently checked segment boundaries. All data searches and arithmetic in generators are only witnesses; the mathematical acceptance is Lean checking of the generated statements. 

## 07:54 UTC checkpoint
Exact normalized row membership and table match checked separately against the accepted normalized closure (Raw139E0ZeroRAMatch.lean); do not mix the two object closures without rebuild. Fast packed checker margin optimization proved: n+6≤B suffices for weightOK. All 24 child source families generated; 126/126 modules for B1 codes 4,5,7,11,13,14,15,16,17 compiled locally. Full parent still conditional. CI 45778357716 stopped at fast.py source hash assertion. Replace textual patching with exact compressed, locally checked Fast source. No mathematical rejection in that run.
