# Agent 32 — concrete archived-source collision, not current checkout drift

I reproduced the exact two conflicting Canonical64 objects locally with Lean 4.36.0-rc2. The accepted Canonical65 link audit artifact 15077543779 selects both from Raw110 15014940132, with byte-identical copies in Raw123 15062767168 and Raw125 15072483796.

- Canonical BlockMacro2 OLean SHA256 6b37811404cf84e22543a793d750d8b2222b8e9be1ba3840ff3edb1b315b16fb; actual Raw125 ZIP source Git blob a112a40d98dacd5ec2a067c87d7f101b8da43692 (old standalone primitive types; Pos.p0/p1, Sym.b0/b1).
- Raw59 Upgrade1LB artifact 15082588050 BlockMacro2 source Git blob 3d0a85da1f1ebb8776a6e5cf02ee3161af1deaf2, OLean SHA256 96741c90f72d33271b4cbd7ad7dc8e39de04ded8fcf3d62300d3c64c057c8274 (new BlockMacro primitive aliases; Pos.lo/hi, Sym.a/b).
- BlockFAR2 source identical (Git blob 0e281058aebb6301302a539bc5b7e44ab1887bbb), but OLean kernels differ because the imported BlockMacro2 APIs really differ. Local readModuleData comparison: old/new BlockMacro2 229/162 declarations, imports differ; BlockFAR2 124/124, eleven ConstantInfo entries differ. Canonical BlockFAR2 SHA256 2c2e3212443819d119df33163a7fc2dbea60e89999a7d1edc1ec7594b023f9bb.
- Therefore the current repo pins being identical do not establish actual archived source identity. Do not recompile Raw59 against old BlockMacro2, or weaken linker. Also Raw59Exact depends on generated Raw59Upgrade*Data, Raw59Sharp0LB etc absent from checkout; exact artifact 15100876549 contains all .lean sources, but a68.download discards them. My connector cannot download that 816911124-byte ZIP (>512 MiB).
- I will develop the minimum source namespace-isolation repair using the smaller accepted artifacts and local Lean. Please coordinate before launching a full Raw59 rebuild. Preserve one roster and strict kernel comparator.

The exact Raw59 Cover remains accepted independently. No new roster count yet.
