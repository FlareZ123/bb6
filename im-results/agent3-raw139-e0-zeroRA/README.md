# Raw139 E0=0RA candidate closure and checked packed audit

Exact proposed normalized cylinder: [7,24,11,24,14,24,24,16,1,11,24,24], codes 4*q+2*w+r, 24 unknown. Six holes = 244140625 literal completions. First unknown query B1 at time 9. Full 24 ordinary branches, no state quotient.

C++ bounded census (250 steps, cycle period <=120, 1/2-state FAR): 557737 nodes including root, 23239 internal splits, 534498 terminals. Terminal counts: 402941 translated cycles, 103456 last-hole queries, 24549 FAR, 3552 open. Python classification gives 1883 block invariants (some reflected), 1601 FAR, 59 cycles, nine late queries. Only one late query has multiple holes: [7,24,11,22,14,17,24,16,1,11,3,20], A1 at 4808. All 24 ordinary children classified (17 FAR, seven last queries at 4809/4810); halt child charged separately. Proposed common weighted bound 321796, based on exact last-hole query 321790 of [7,2,11,19,14,20,13,16,1,11,24,10] at F0. No open candidate terminal. **Full six-hole cover not yet formally checked; no frontier count change.**

## Checked reusable result

Agent3PackedAudit.lean inside source.tar.xz is kernel checked in Lean 4.36.0-rc2, SHA256 9209161803c20545ee295076a523f703c3896294458c939e2b5104bb702c3761. It imports ZipAuditCore and FastThreeHoleAudit, defines packed tape execution, proves packed_read, pcycle_sound, pquery_sound, and PAudit/pcheck_sound (allows exact-table-matched already checked semantic bounds at leaves). Axioms: packed_read and pcycle_sound [propext, Quot.sound]; pcheck_sound [propext, Classical.choice, Quot.sound].

The longest trace and its leaf cover also compiled successfully: BB6.Agent3E0RALong.trace and .cover, standard axioms. 315 segments (1024 moves except final remainder), 20 Part modules, 20 explicitly indexed Join modules, one final Cover. The original monolithic pjoin composition OOMed. Explicit indices and group theorems eliminate giant definitional reduction. Exact final packed state q=5, head=32, left=0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe, right=2.

## Reproduction

Extract source.tar.xz in this directory (SHA256 fb2d8506761f3a7843e59d16202ad069f68fba835dca9e5b03fe46623dd58b7d). Generator scripts use existing Agent48 scan.py/blockcert.py and the Agent3 C1 emitter; all Python generators are untrusted. C++ census adapted from Agent6.

g++ -O3 -std=c++17 census.cpp -o census
./census 1 > counts1.txt
python classify.py
# hard.jsonl, latechildren.json, latehard.jsonl bundled from successful search; hard.py regenerates hard.jsonl
python long.py
python emit_family.py 11 18 8 # or all integer B1 codes 0..23

Set A3_BUILD to the target build directory or use default generated/. Compile Agent3PackedAudit.lean into the build directory first. Use original C1 batch artifact 15083884536 (run 45746968139, source revision 24307ed48c90f18938778cac530c5c3213af2203, ZIP SHA256 b5141e994a4fbbf56d1f226ccd64df425df6d9816b6fcc1282b7ba7e63dea243). Compile original SparseZipper, SweepPumping and ZipAuditCore sources (available in normalized artifact 15093190882, run 45767740664) against that coherent closure, not the separately built objects. Compile A3E0RALongBase, all Part, all Join, Cover. Then compile modules in modules{b}.json order. B1=11 generator tested: 929 splits, 39 initial open leaves, 5 block shards, 104 small audit chunks, max 385 nodes. Full family compilation pending at checkpoint. Python partition checks all open table keys against witnesses. Need ensure generated families, normalized exact row match and complete root proof before integration. No fresh CI build claimed.

Long cover generator uses actual trace endpoint and independently checked segment boundaries. All data searches and arithmetic in generators are only witnesses; the mathematical acceptance is Lean checking of the generated statements. 
