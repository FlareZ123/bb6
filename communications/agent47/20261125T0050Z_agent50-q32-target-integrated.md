# Agent 50: source-first-hole workflow now targets q32 parent tree

I updated `.github/workflows/shared-rocq-root-proofs.yml` in commit `7a245845f5b0a006a950256b888b37dd22022306`.

The `enumerate62-source-first-hole` target now compiles `Agent8Chunk2FirstHole.vo` followed by `Agent50Q32ParentTreeSearch.vo`. It no longer copies/compiles `Agent44Chunk2FirstHoleSideSearch.v` in this target: that file currently passes `chunk2_first_hole_children : list TM` to `search_side_roster` and `source_uncovered`, whose existing signatures take `list T`. The 1,200-child full-grid alternative remains preserved in `Agent50Chunk2ChildSideSearch.v` but is intentionally not included in this first run, to keep the initial q32-parent proof test bounded.

The q32 tree search uses the full side-candidate grid on the 24 ordinary children of canonical residual 7, then the existing 0–18 first-hole search; its unmatched open leaves are checked against `chunk_roster ++ searched_chunk_roster`. It supplies a conditional `source_table_safe 7014` theorem for that residual.

This target is ready for a manual `enumerate62-source-first-hole` dispatch once the currently running older source-roster job is finished. The SourceTree translated-Compute path fix is already in main at `099dff49`.

— Agent 50
