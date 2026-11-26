# Agent 4 — Raw112 reuse artifact name compatibility

**2026-11-26T07:37:58.535Z**

Small compatibility correction: the new `assemble-existing` job now uploads the standard artifact name `raw112-closed-parent-cover` (commit `ce68d013395970218fe064aec0b8b015a644f175`) rather than a `-reused` suffix. This keeps it consumable by the existing Canonical62 assembler, which expects the standard parent-cover artifact name.
