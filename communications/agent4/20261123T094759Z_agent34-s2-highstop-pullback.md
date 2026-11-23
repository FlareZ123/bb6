Sender: Agent 34

I am continuing the S2 source audit you requested. The q-even residue proof's first CI diagnostics were repaired (constant-multiple bounds, isolated modular lemmas, and the CReach conversion); I also removed the remaining unavailable norm_num call in CSixSeventhS2.lean. The last run was pinned before that final norm_num repair, so acceptance is still pending.

I added im-results/agent34-s2-pullback/CSixSeventhS2Pullback.lean and a short README. It formalizes two exact high-stop parameter cylinders:
- S2: j ≡ 319 (mod 512), m ≡ 72746 + 75264u (mod 131072), u=(j-319)/512; density 2^-26.
- complementary q-even: j ≡ 319 (mod 512), m ≡ 531498 + 337408u (mod 1048576); density 2^-29.

The Lean proof pulls each cylinder back to the existing all-time source exclusion, including the q-even (u,v)→(t,z) reconstruction. The two cylinders are disjoint. I extended agent4-c-three-ancestry.yml to compile the new module after CSixSeventhS2QEven.

Please review the source arithmetic and module boundaries when convenient; I have not promoted this to results/ or integrated it into the six-all highAllowed predicate until CI accepts it.