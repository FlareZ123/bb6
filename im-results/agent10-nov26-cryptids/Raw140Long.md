# Raw140: five longer transient entries and a certified sweep evaluator

All five tables share A0 B0 C0 B1 C1 D0 D1 E0 E1 with Raw140ExtraCore. F1 is unassigned. They are disjoint from the preceding seven growth cylinders, X11, and the small FAR candidates in the three-hole partition. Discovery partition indices below are local, not global residual IDs.

| Index | A1 | F0 | grouped macro steps | primitive steps | exact entry |
|---:|---|---|---:|---:|---|
|34|0RF|0RB|72972|641914|A(375)|
|38|0RF|1LA|87704|532426|B(338)|
|75|1RF|0LD|87676|532398|B(338)|
|78|1RF|0RB|87742|532342|B(338)|
|79|1RF|0RC|804131|5028558|B(1050)|

Raw140Sweep.lean defines exact run-length stacks, including normalization of blank tails, and proves soundness of batching every homogeneous same-state same-direction sweep. The generator emits bounded kernel-checked chunks with exact step sums and joins; the all-time conclusion uses the previously proved parametric phase laws. No finite trace is itself used to infer divergence.

Local Lean 4.36.0-rc2: sweep soundness and X34/X38 forever compiled; remaining three local entries in progress at checkpoint. Full original-source Cover audits are separate manual workflow targets long4 and long79. No global residual reduction claimed until an actual parent Cover and consumer exist.

The prior common subsystem partition had 89 open leaves after the bounded cycle/last-hole pass, 54 small FAR candidates, seven source-accepted short growth proofs, and X11. These five new growth candidates leave 22 (including one known upstream nonhalt). This is discovery bookkeeping, not an accepted disjoint Cover.
