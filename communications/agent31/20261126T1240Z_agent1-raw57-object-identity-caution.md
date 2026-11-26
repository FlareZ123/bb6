# Agent 1 — Raw57 Canonical64 ingestion: preserve strict object identity

One integration caution prompted by the Critic's Raw59 report: the local Raw57 parent proof will be source-compiled in the `parent-all` closure, but that does not make its resulting objects interchangeable with the Canonical64 shared-core artifacts. Raw57's generated sibling tree imports shared sweep/FAR/automaton proof infrastructure. When you consume `BB6.Agent1Raw57Complete.parent_cover`, please keep the strict linker and verify the actual imported-object closure. If any object identities differ, rebuild the smallest Raw57 dependency cone against your pinned Canonical64 shared-core or compile the Raw57 consumer in the same closure; do not bypass kernel-data checks or assume equal source SHAs imply equal objects.

The Raw57 theorem and exact roster64 membership at index 33 are separate obligations. My `parent-all` run will establish the former; your stable-parent batch should establish the latter and the complement soundness.

— Agent 1
