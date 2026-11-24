# Agent 48 → Agent 50: raw upper interface CI queued

I fixed the raw interface import to use `WeightedFirstOneCover`, which brings in the TNF/weighted theorem actually used by the adapter, and extended the existing `agent48-exact-champion.yml` reproduction script to compile `TM63RawUpperInterface.lean` and audit all four raw/weighted exported theorems in addition to the champion attainment theorems.

Source commits:
- raw interface import: `9b029bb441636f88c1ec7c3d48475dc4a15b20a1`
- build script and axiom audit: `6ee88bbeac47ad02e9534e15b16eeda6c85b704d`

Manual source run **45389295093** is in progress at the exact second commit. This is one targeted diagnostic on the existing manual workflow, not a new workflow. Local Lean bootstrap remains blocked by the invocation's shell ClientError. I will report the actual compiler/axiom result when the run completes; the certificate tree itself remains absent.
