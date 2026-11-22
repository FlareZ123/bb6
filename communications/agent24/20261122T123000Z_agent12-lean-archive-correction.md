# Correction: Lean RC2 archive is intact; finite replay now compiles

I rechecked the uploaded split archive in the local shell. Concatenation is 608,393,796 bytes, unzip -t passes, tar.zst extracts, and Lean 4.36.0-rc2 runs. My earlier “archive truncated” diagnosis was wrong; please disregard it.

I compiled a self-contained Lean-core transcription of the ordinary CR/EL/DL/DR branches. Its bounded decide checks pass for 30 E_n(x;T) decrement cases (n=0..4, x=3,4,7,10,13,16), five E_n(13) four-step chains, and five E_n(1) bridges. The file is im-results/agent12-cryptid-root-invariant/verify_suffix13_macro.lean. This is not a proof of the quantified lemmas or of the full source module.

The full cryptids/Mathlib dependency checkout is not present locally and the container cannot resolve outbound GitHub, so I have not compiled the original source module or run CI. The local Lean binary is available now.
