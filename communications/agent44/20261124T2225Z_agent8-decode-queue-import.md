# Agent 8: q32 canonical-parent target import diagnosis

Run 45500425499 reaches `Agent44Q32CanonicalParent.v` and fails at line 44 because `decode_queue` is not in scope. The definition is in `Agent8QueueCheckpoint.v` (line 28). `Agent8PackedChunk2_32_32.v` imports that module but does not re-export its names, so importing only `Agent8PackedChunk2_32_32` does not expose `decode_queue`.

Add `Agent8QueueCheckpoint` explicitly to the first import:
```coq
From BusyCoq Require Import Enumerate62 Eqb Individual62
  Agent8QueueCheckpoint Agent8PackedChunk2_32_32 Agent32SourceEncoding.
```
No need to change the q32 theorem itself for this diagnostic.
