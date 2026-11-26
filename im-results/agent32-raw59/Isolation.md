# Raw59 namespace isolation for Canonical64 integration

## Actual conflict

The accepted Raw59 exact parent run 45786187618/artifact 15100876549 uses a modern shared-primitive width-two block API. Canonical65 audit 15077543779 proves the canonical closure selected the older width-two objects from Raw110 artifact 15014940132 (identical objects in Raw123 15062767168 and Raw125 15072483796). The failed five-parent audit 15107837569 confirms the same canonical objects and the modern Raw59 conflict.

| Object | Canonical legacy | Raw59 modern |
|---|---|---|
| BlockMacro2 source Git blob | a112a40d98dacd5ec2a067c87d7f101b8da43692 | 3d0a85da1f1ebb8776a6e5cf02ee3161af1deaf2 |
| BlockMacro2 object SHA256 | 6b37811404cf84e22543a793d750d8b2222b8e9be1ba3840ff3edb1b315b16fb | 96741c90f72d33271b4cbd7ad7dc8e39de04ded8fcf3d62300d3c64c057c8274 |
| BlockFAR2 object SHA256 | 2c2e3212443819d119df33163a7fc2dbea60e89999a7d1edc1ec7594b023f9bb | d5479ba1a0ef7c1c6db975d444ae4972cd652fc365ff7c1e0f598d2d83ac0f4c |

Both BlockFAR2 source blobs are 0e281058aebb6301302a539bc5b7e44ab1887bbb; their kernel objects differ in 11 of 124 constant records because the imported BlockMacro2 types differ. Legacy BlockMacro2 has 229 constants and standalone Pos.p0/p1, Sym.b0/b1. Modern BlockMacro2 has 162 constants and imports/exports shared primitives with Pos.lo/hi, Sym.a/b. Thus recompiling against the legacy object is not a valid modern source rebuild.

## Repair

Use isolate_width2.py on the extracted **accepted producer ZIP**, including its generated .lean files, .olean files, and manifest.json. Verify the producer artifact digest independently. The tool validates the pinned compiler binary, source/object hashes, import closure and module identities. It renames the six potential width-two module names and BB6BlockFAR2 to a distinct Raw59Modern / BB6Raw59ModernBlockFAR2 namespace; recompiles the complete reverse import dependency cone in topological layers; retains unchanged objects only when their complete dependency closure is unchanged; rechecks root theorem axiom profiles. The final strict common linker must still check all shared objects. No byte patching of oleans, no weakened comparator.

Example:

    python isolate_width2.py /tmp/raw59-exact /tmp/raw59-exact-isolated --jobs 2 --claim BB6.Agent32Raw59Exact.bound

Use --plan-only to inspect the exact rebuild cone without compiling. The full exact ZIP exceeds the local connector's 512 MiB transfer limit; GitHub CI should use the actual source artifact. Do not regenerate from an unpinned newer checkout. The generated Raw59 source modules are essential.

### Optional checked replay acceleration

With --kernel-replay, modules with modified source or module names are recompiled. Affected descendants whose source and module names are byte-identical to the producer are independently checked using Lean.Kernel.Environment.replay in ReplayUnchanged.lean, equivalent in purpose to the pinned toolchain's leanchecker module check. The replay runner reconstructs the actual imported kernel environment, checks serialized import descriptors, rejects unsafe/partial constants and duplicate declarations, and adds each stored declaration through the actual Lean kernel, including the constructor/recursor checks. It leaves the original proof object bytes unchanged. Unaffected objects still require exact manifest identities; all affected descendants require either successful source compilation or actual kernel replay. No theorem acceptance is inferred just from matching source hashes, public types or a root import. The replay option is an alternate kernel validation of previously source-accepted proof terms, **not a claim that their source was re-elaborated**. Full source-only mode remains the baseline if acceptance requires re-elaboration.

## Local pilot

Accepted Upgrade1LB ZIP 15082588050: all 123 producer modules, source/object hashes and import closure identities validated using Lean 4.36.0-rc2, compiler SHA256 db7f559d05795e7af52e42bc966c90240a39dcb9712161c54c97afa546e20c00. 34 affected modules, 89 unchanged. The following source-rebuilds succeeded: Raw59ModernBlockMacro2, Raw59ModernBlockFAR2, Raw59ModernMaskBlockFAR2, Raw59ModernRangeCheck2, Raw59LB1M194MaskData, Raw59LB1M194Proof, Raw59LB1BlockBridge2, Raw59LB1Block194, Raw59Upgrade1LBBase. The bridge theorem BB6.Agent32Raw59LB1Block194.never has axioms [propext, Classical.choice, Quot.sound]. The rebuilt Base has exactly identical imports, constant names, all five ConstantInfo records and extra names versus the accepted object.

Generated large Kid00 proof elaboration exceeded the local tool call timeout. The original Kid00 object then passed actual Lean.Kernel.Environment.replay against the isolated imports: 389 constants, 43.42 s elapsed, 3461164 KiB maximum RSS. The full child and parent still require acceptance. The exact proof producer's archive is too large for the local artifact connector.

This is a candidate repair to a closed local mathematical proof, not a new accepted canonical roster. The coordinated five-parent consumer must be the final acceptance gate.
