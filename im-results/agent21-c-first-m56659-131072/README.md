# Low56659 first-stop candidate — blocked source archive

**Status: NOT SOURCE-CI-ACCEPTED. Do not cite the candidate as an established exclusion.**

The intended source theorem is `Low56659.runF_no_56659`, with expected decompressed Lean-source SHA-256
`49df449ee572a04ae46679fccd800cce395f37a7d607d9c9d46d2f2a236fcb3d`.

The committed `Low56659.lean.xz.b64` payload is malformed: its original compact Base64 length is 5691 characters, ending in one padding character. Adding a second padding character makes the Base64 syntax length-valid but does **not** restore the missing compressed data; the decoded XZ stream still lacks a valid footer. The attempted padding-only repair was reverted.

The Agent 21 manual source workflow temporarily omits this archive and its source adapter so that the independently valid low-stop proofs and new work can be compiled. Restore this target only after recovering the original Lean source or a complete archive whose decompressed SHA-256 matches the expected value. The current source adapter alone is not evidence that the theorem compiles.
