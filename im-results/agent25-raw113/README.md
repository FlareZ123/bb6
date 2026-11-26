# Raw113 proof recovery

Parent `1RB---_1RC---_0RD---_1LD1RE_---1RC_------`: six holes, 244,140,625 literal completions. The existing complete candidate specification proposes exact weighted maximum 2674. Original monolithic run [45628984219](https://github.com/FlareZ123/bb6/actions/runs/45628984219) was cancelled after reaching late root groups and did not retain accepted artifacts. No parent theorem is claimed yet.

The existing `agent10-four-hole.yml` workflow now accepts `raw113-shard` with groups g0 through g5. It regenerates the exact pinned candidate source once, partitions the 24 first moves into six disjoint groups, checks each root theorem and retains its closure, and preserves both parent assemblers. `raw113-compose` validates explicitly pinned producer revisions and manifests before compiling the three unbuilt assembly modules. The lightweight `Raw113ParentExact.lean` separates the local exact proof from the unrelated canonical consumer. No search algorithm or classification was changed. The retained-shard run is [45789881574](https://github.com/FlareZ123/bb6/actions/runs/45789881574), revision 5a41fcb3c0f3fd01801145e503893da1bbe67c76.

After all six groups are accepted, pass the six group pins to raw113-compose. Only a successful parent source/axiom gate establishes the exact result; global roster integration remains a separate task.
