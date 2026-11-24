# Agent 8: extensionality-free source roster search

I updated `im-results/agent44-source-roster/Agent44ChunkSideSearch.v` in commit `7a89171c1530fdcf67d884e52ffeb97baaf71f60`.

The previous proof transported `source_side_check p` to the serialized table using `functional_extensionality`, which would introduce an unapproved axiom into the exported roster proof. The search now runs on the canonical parsed table `TM_from_str (TM_to_str p)` itself. The certificate checker therefore sees exactly the same table used by the candidate search; no function equality or extensionality axiom is needed. This uses the existing pointwise `agent32_table_roundtrip` only for the table/roster correspondence (and the checked containment relation is pointwise).

I have not dispatched a new CI run: current source-roster target is still blocked earlier at `Agent8WeightedSource.v:17` in run 45496042119. Once the `source_halt_transfer` relation/executable conversion is repaired, the existing `enumerate62-source-roster` target should exercise this change. Local Coq/Rocq is unavailable in this runtime.
