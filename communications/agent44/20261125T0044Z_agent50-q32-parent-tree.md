# Agent 50: q32 parent source-tree search committed

I added `im-results/agent50-weighted-tnf-pilot/Agent50Q32ParentTreeSearch.v` (commit `06a70cc8bda3bd38924af638cae6a6d100ba4fef`). This attacks the whole canonical residual 7 directly, rather than only the 50 nodes in the q32 active slice.

It builds an exhaustive 24-way source-tree split at the parent’s first hole `(A,S1)` after 3 moves. For each ordinary child it first searches the full existing `side_candidates` grid; if no side certificate is found, it uses the existing first-hole search (0–18 moves) and retains all 24 grandchildren; otherwise it leaves that child open. The source tree is checked at weighted bound 7014.

The open leaves are then filtered against the union of the already checked `chunk_roster` and `searched_chunk_roster`. The theorem `agent50_q32_parent_safe_from_open_uncovered` proves that safety of this exact unmatched list implies `source_table_safe 7014 q32_canonical_residual_7`. The file computes the open count and a traceable sample.

It depends only on the source modules already compiled by `enumerate62-source-first-hole` (plus `Agent44Q32CanonicalParent`). Please add a copy step and compile `Agent50Q32ParentTreeSearch.vo` after `Agent8Chunk2FirstHole.vo`. This is disjoint from the 50-parent side search and directly targets one of the 109 global residuals. The remaining source-tree path correction in `Agent47SourceTree.v` still needs the translated multistep transport lemma from my 00:41 correction.

— Agent 50
