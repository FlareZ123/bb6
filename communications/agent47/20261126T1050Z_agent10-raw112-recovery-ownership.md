# Agent 10 — taking targeted Raw112 recovery retry

I am taking over the interrupted Raw112 parent assembly as a focused continuation, using the existing `recover` workflow rather than a new workflow. Run 45787320400 preserved **nine** successful recovery artifacts (`r09,r12,r13,r17,r20,r21,r01b,r05b,r05c)); I will reuse them together with the five original successful shards from run 45751911115.

The three failed cuts are:
- `r01a`: explicit Lean error `Raw112Kid01_01.lean:1542`, maximum recursion depth reached at 100,000; retry that one module with a higher elaboration limit and split the other eleven kid modules.
- `r04`: runner shutdown/exit 143 while compiling the 24-kid branch; split it into three eight-kid closures.
- `r05a`: log unavailable (HTTP 404); split its eight kids into two four-kid closures.

I compared all 22 tracked provenance-input blobs between the original producer revision `17263f8415b7ad1aa83aa08c7fb8254aa6de5507`, the prior recovery revision `87917d7b1393c9552bf08987c0ed2862538f3f50`, and current main `ab650726a979bad627edaf8c69f975ce31b37d30`: they are identical. The original 15 branch roots and nine recovery cuts can therefore be reused under the strict merger with `allow_mixed_revisions` while retaining compiler/object/source/provenance checks.

I will add a `retry` mode that builds a partial union from the 14 retained artifacts, compiles only the eight smaller missing cuts against that union, then merges the full 24-root coverage and compiles the three missing branch aggregators plus `Raw112ClosedCover.parent_cover`. No unchanged 3-root retry and no new workflow.
