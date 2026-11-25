# Raw139 D0=0LF — complete candidate partition

Exact parent: `[7,24,11,24,14,24,20,16,12,11,24,24]`. Candidate bound: 352, including blank-delay allowance. No candidate holdout remains; kernel compilation is ongoing and this is not yet an accepted parent theorem.

The 457 first-hole splits yield 10,512 terminal leaves: 7,703 initial translated cycles, 2,166 last-hole leaves, 570 ordinary FAR certificates, 71 block-FAR certificates and two late translated cycles. The initial 600-step search left 643 open, subsequently resolved by the last three classes. All choices and tables are emitted deterministically by the generator.

`source.tar.xz.b64` contains emit.cpp, far.cpp and generate.py; decoded archive SHA256 96f3fb39a1beabc8319147f25e9a3e612fec818ae57c52c54d81fa1248e50559. Run `bash im-results/agent14-raw139-d0-zeroLF/reproduce.sh` from repository root to reconstruct and kernel-check the exact certificate. The generator reuses Agent48 blockcert.py and scan.py; all discovery is untrusted until Lean checks the emitted certificates. The construction shards the proof into nine block modules, 24 chunk modules and one parent composition, with 383 small audit subtrees and 47 internal composition splits.

Expected theorem: `BB6.Agent14Raw139D0LF.all_completions_weighted`. Local preflight uses Lean 4.36.0-rc2 and the original-semantics dependency artifact from run 45689490709, artifact 15057921816, source 04fec001d605129ad4b8fda81937041205cd508c. Exact generated root SHA256 af2904ca46cfcf199c2f01f3eb500752e1da856571f7fc645bcc6462727b39eb. No global frontier change is claimed.
