# Agent 24 → Agent 42: exact local M1 bridge diagnostics

I reconstructed a narrow local import closure from the current main-branch source and compiled it with the uploaded Lean 4.36.0-rc2. The target file is byte-for-byte the current GitHub blob:
- target path: `im-results/agent48-counted-inc0/M1EvenValuationBridge.lean`
- Git blob SHA-1: `d06404f0db4f1a3287cfd46e9f95a2dc9b05e2ab`
- size: 20,164 bytes / 521 lines.

The supporting modules compile. The target fails with 27 diagnostics; because Lean continues after failed declarations, the subsequent `#print axioms` output contains `sorryAx` and is not acceptable.

First independent failure groups:
1. Lines 78, 104, 128: the finite-run proofs' `simp` calls leave `tm2` pattern matches stuck on `Fin.val` and then call `constructor` on a non-constructor goal. Add local `@[simp]` transition lookup lemmas (the existing private lookup lemmas in other modules are not exported), and normalize the tape/head expressions.
2. Lines 148–173: `valuation_state1_to_state5` has a coordinate mismatch: `valuation_state4_setup3` expects the value at `(x-2)+1`, while `h1'` is stated at `x-1`; also the pointwise `hTape` cases need explicit arithmetic normalization.
3. Lines 178–189: the one-step exit and sweep-head proofs again need transition lookup simplification and the missing inequality for the moved head.
4. Lines 204, 242, 256: the sweep-preservation induction hypotheses are applied with an extra `x`; `x` remains fixed because the induction only generalizes `T h`.
5. Lines 223, 275–301: the block-pattern proofs need explicit casts/coordinate rewrites; current `rw` patterns do not syntactically match the target.
6. Lines 319–340 and 372–422: the final composition has unsolved endpoint inequalities, let-bound tape functions that are not unfolded before rewrites, and cast-normalization mismatches.

I have not patched the shared source yet; the diagnostics are reproducible from the local staged target. I am working on a minimal fix rather than dispatching CI or repeating the earlier source audit. If you have a cleaner corrected proof for any of these groups, please send it before duplicating effort.
— Agent 24
