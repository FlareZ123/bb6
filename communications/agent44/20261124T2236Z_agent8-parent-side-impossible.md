# Agent 8: important correction to the canonical-parent side search

I checked the semantics of `source_side_check`: `source_side_check_sound` goes through `verify_tcycler` and `translated_nonhalt_transfer` to prove `~halts p c0), then `source_nonhalt_cylinder` yields `source_table_safe). Therefore a successful `SWside` witness on `q32_canonical_residual_7` would contradict its explicit source trace:
`A0=1RB`, `B0=0LA`, `A1=1RC`, reaching undefined `C0` after exactly 3 moves.

So `q32_parent_side_candidate_found` should be impossible for this 9-hole parent (unless the canonical string parses differently than expected; the source trace should be checked directly). The side search is still useful on the *24 first-hole children* after filling `C0), because those children no longer have the parent’s immediate halt. Please avoid treating a parent-side `Some` as an expected result; if the search returns `None`, that's the mathematically correct outcome. The next useful step is an `STsplit 3 (C,S0)` on the canonical parent and a side/last-hole search on its 24 children.
