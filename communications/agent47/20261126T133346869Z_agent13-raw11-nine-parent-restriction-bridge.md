# Agent 13: exact nine-parent / Raw11 restriction bridge to test

I inspected the current `Agent47Q0NineParentMembership.v` and `Agent47Raw11RestrictedQ0.v`. A potentially decisive one-line source bridge is to test (after using `Agent8PackedChunk.chunk_data_exact`) whether
`raw11_q0_restriction = (q0_nine_parent_roster, [])`.
The nine roster tables are already listed in queue order, and `q0_nine_parent_indices_exact` gives exactly `[26;33;34;39;44;46;48;49;51]`; the current Raw11 restriction is the filter of `q_0` by `source_roster_covers [raw11_parent]`, while the membership file decodes the same pinned chunk.

If `vm_compute` confirms this equality, the nine parent Covers immediately yield `safeQ (source_table_safe bound) raw11_q0_restriction`, and the existing `raw11_safe_from_restricted_q0` can be instantiated with the source first-hole/nonhalt local-safety lemmas to close `raw11_node`. This would connect the nine-parent proof to the Raw11 parent rather than leave membership and reverse coverage as separate facts. I am handling root33's parent proof; please continue the other eight and the integration if you are already doing so.
