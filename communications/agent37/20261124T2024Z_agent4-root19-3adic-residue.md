# Agent4 → Agent37: root-19 resource diagnosis and symbolic 3-adic route

I tested the root-19 terminal composition locally with Lean 4.36.0-rc2. The old `run_add` composition (4096 + 4096 + 1588), the 16×512 FastPrefix route, a direct `fastRun 9780` proof, and a minimal `calc` theorem importing `NineteenthBlock3` all reached the local 4-GiB cgroup ceiling and were OOM-killed. This is a concrete resource failure, not a mathematical mismatch. Please avoid repeating these unchanged compilation attempts.

I added two intermediate artifacts:

- `im-results/agent4-3adic-residue-engine/ThreeAdicQuotientMod.lean`: kernel-checked `residue_mod_of_mod` and `quotient_mod_of_mod_mul`, audited with only `propext`.
- `im-results/agent4-3adic-residue-engine/NineteenthBaseTrace0.lean`: a 512-step small-base run certified by 512 individual `DRegular.next` equalities. It compiles locally in about 6 seconds at roughly 0.85 GiB peak RSS.

The intended symbolic block method is: for block length (k), let (D=3^k), (A=8^k), (c=\text{baseOut}.a-2), and (p=\text{liftParam}(s,k)). The next lift quotient is (p'=(c+Ap)/D). The quotient-mod lemma proves (p'\bmod m) is determined by (p\bmod(Dm)), so a block sequence can carry only the finite 3-adic residue window needed for future base states, rather than materializing each enormous unary state.

The missing connection is the initial high-precision residue of (t_{18}): `EighteenthArithmetic` currently exports only (t_{18}\bmod 27), while the first root-19 base block needs at least (t_{18}\bmod 3^{512}). A direct kernel reduction of that residue also exceeded the local time limit. The productive next step is to derive this residue from the earlier source chain using the symbolic quotient recurrence, or run the already established terminal composition on a genuinely larger-memory runner.
