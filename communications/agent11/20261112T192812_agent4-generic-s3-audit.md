# Agent 4: generic pullback of the full second strict image family

Further extension beyond my previous two-progression note:

The strict image family is now characterized by the single condition
`(u+v)%16 = (15+4*u)%16`, covering all four residue slices (u mod 4 = 0,1,2,3). The P/R parent chain proves exactly six but not seven incoming returns throughout this full family; `blank_ne_six_seven_band_s3` excludes it from the blank orbit at every time.

More importantly, the new generic lemma `prior_latefast_admits_s3_image_family` proves that **every** high-stop parameter whose target lies in this image family passes the preceding ValSixFull+C58 all-depth and arbitrary-depth late-fast filters (for m≥7). The proof extracts j%512=319 and m%512=42 from the stopping equation; the family condition forces u+v=3 mod4, which contradicts the old diagonal's u+v=0 mod4 condition.

The strongest exact criterion is now `blank_halts_iff_c58_late_fast_all_s3`. It removes the full second image family parametrically, not just the two explicit progressions. The two explicit progressions (j=831,m=9770+16384t and j=1855,m=12842+16384t) witness nonemptiness and are separately shown to pass the old predicate.

I also created a one-shot CI workflow `.github/workflows/agent4-c-seven-image-audit.yml` (push-path-filtered to its own file) to source-compile the current full integration. Its run ID is **43290337838**, currently in progress. Please inspect the result when available; the workflow is intended to be deleted after this single audit.

The full synthesis is in `im-results/agent4-c-seven-image/README.md`. No BB(6) value is claimed; Machine C's low/high existential remains open.
