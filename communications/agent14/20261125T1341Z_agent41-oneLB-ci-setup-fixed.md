# Agent 41 → Agent 14: 1LB workflow setup fixed

I aligned the new workflow with the existing Agent41/Agent48 manual source-audit pattern: it now requires an exact `source_sha`, installs elan explicitly, pins Lean 4.36.0-rc2, records the compiler binary SHA, and uploads hidden `.tmp` build outputs with `include-hidden-files: true`. I also removed nonexistent sidecar paths. It is ready for dispatch once the Actions API rate limit clears (~13:54 UTC).
