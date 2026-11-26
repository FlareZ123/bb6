# Raw139 D0=0LF — complete kernel-checked cylinder

Exact parent: `[7,24,11,24,14,24,20,16,12,11,24,24]`. **WeightedBound 352**, including blank-delay allowance, for every compatible completion. All 34 modules compiled successfully in the original-source kernel locally on 2026-11-26 at 00:03 UTC. Independent CI and global roster integration are pending.

The 457 first-hole splits yield 10,512 terminal leaves: 7,703 initial translated cycles, 2,166 last-hole leaves, 570 ordinary FAR certificates, 71 block-FAR certificates and two late translated cycles. The initial 600-step search left 643 open, subsequently resolved by the last three classes. All choices and tables are emitted deterministically by the generator.

`source.tar.xz.b64` contains emit.cpp, far.cpp and generate.py; decoded archive SHA256 96f3fb39a1beabc8319147f25e9a3e612fec818ae57c52c54d81fa1248e50559. Run `bash im-results/agent14-raw139-d0-zeroLF/reproduce.sh` from repository root to reconstruct and kernel-check the exact certificate. The generator reuses Agent48 blockcert.py and scan.py; all discovery is untrusted until Lean checks the emitted certificates. The construction shards the proof into nine block modules, 24 chunk modules and one parent composition, with 383 small audit subtrees and 47 internal composition splits.

Accepted local theorem: `BB6.Agent14Raw139D0LF.all_completions_weighted`. Local preflight uses Lean 4.36.0-rc2 and the original-semantics dependency artifact from run 45689490709, artifact 15057921816, source 04fec001d605129ad4b8fda81937041205cd508c. Exact generated root SHA256 af2904ca46cfcf199c2f01f3eb500752e1da856571f7fc645bcc6462727b39eb. No global frontier change is claimed.

Exact local parent proof output:

```
'BB6.Agent14Raw139D0LF.hR' depends on axioms: [propext, Classical.choice, Quot.sound]
'BB6.Agent14Raw139D0LF.all_completions_weighted' depends on axioms: [propext, Classical.choice, Quot.sound]
```
All nine block, 24 chunk and one parent module compiled without errors or `sorryAx`. Exact generated root and source archive hashes match the pinned reproduction inputs. The independent clean-source CI uses existing Agent48 workflow `kind=d0`, `sibling=ZeroLF`.

## Independent clean-source audit

Run [45726077932](https://github.com/FlareZ123/bb6/actions/runs/45726077932) completed successfully at source pin 10600f0067436e573ad18d75fa8a49f1b3d63793. Artifact 15075155906, `raw139-d0-ZeroLF-certified`, SHA256 3a88afc2f88a89ebb321832b71bb03c3e8984431ebc38598280f64d78f33f55d. The entire weighted bound 352 parent theorem is now source-accepted; roster graft remains separate.
