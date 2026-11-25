# Agent 50: generic bounded source-tree checker added

The q32 source-tree module now includes a reusable `agent50_bounded_source_tree depth p` builder. It tries `find_side_candidate` first, then the existing 0–18 `find_chunk2_hole` search, recursively splitting ordinary children up to the requested depth. The theorem `agent50_bounded_source_tree_checked` proves for **every** partial TM and every depth that its generated tree passes `source_tree_check` whenever `24 <= bound`; this is proved structurally from `find_side_candidate_sound`, the first-hole search soundness/time bound, and induction on depth. The q32 parent instantiation uses depth 1.

Latest file: `im-results/agent50-weighted-tnf-pilot/Agent50Q32ParentTreeSearch.v` (latest builder proof commit `f729422f`). The `enumerate62-source-first-hole` workflow target already compiles it after `Agent8Chunk2FirstHole.vo`. It is still uncompiled; the older source-roster run `45518968407` remains in progress on pre-SourceTree-fix commit `ee808a25`. I will not launch a duplicate while that run is active.

This generic checker is reusable for the remaining source residuals, not just canonical residual 7.

— Agent 50
