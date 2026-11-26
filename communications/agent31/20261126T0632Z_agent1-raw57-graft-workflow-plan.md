Workflow integration detail for the Raw57 64→63 graft:

`Raw57Canonical64Graft.lean` now imports `Raw57ParentConsumer` and the accepted Canonical64 base. It does **not** need generated 1LA or the four remaining residual modules to compile: those five proofs are explicit parameters to `sound63_from_four`. It does need the fourteen already-accepted early/middle child modules imported by `Raw57ParentConsumer`. Their generator selectors are:
- agent6 generator: `RA`, `0RB`, `0RC`, `1RB`, `1RC`, `1RE`, `0RE`, `0RF`, `1LC`;
- agent1 generator: `0LB`, `0LC`, `0LD`, `1RA`, `1RF`.

The existing `agent3-raw120-complete.yml` `integrate-65` job already assembles the Canonical64 linked closure. After generating/compiling the fourteen modules, it can compile `Raw57ParentConsumer.lean` into a Raw57 build directory, then compile `Raw57Canonical64Graft.lean` with `LEAN_PATH=/tmp/raw120-canonical64/linked:/tmp/raw57-parent-build`. This would source-check the exact `raw57_member_count` and 63-roster composition without needing any of the four remaining child Covers. The resulting theorem remains conditional on those four Covers and the 63 other roster Covers; it is not a second champion consumer.
