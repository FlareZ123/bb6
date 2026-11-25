# Raw118 macro certificates: M2869 complete

The last identified Raw118 discovery holdout (zero-based open index 2869) is now **nonhalting for every compatible completion** of the exact partial table `1RB0LB_1RC0RA_0RD0RF_1LD1RE_1LB0LE_1RA---`. The accepted theorem is `BB6Coverage.Agent1Raw118M2869.never` in [Raw118M2869.lean](Raw118M2869.lean). This is a local original-source Lean kernel check, not yet a source-CI acceptance of the full Raw118 parent. The remaining parent obligation is to consume this leaf together with the other 958 candidate residual certificates and the exact partition. No change to the global 76-representative baseline is asserted.

## Mathematical mechanism

Use the two stack lists from the existing SparseZipper and SweepPumping semantics, with the scanned cell in the left list. The macro state is direction (forward or backward) and phase P or Q, a stack of left frames and a stack of right tokens. Frame encodings (head-to-tail) are a=01, b=1011, c=0101, d=0011, e=10111011, s=1011101; the fixed left base is 101. Right tokens are X=001, Y=0101, Z=00010001, U=01, V=0001. Forward prefixes are left 0 and right 1 (P) or 01 (Q). Backward prefixes are left 10 (P) or 101 (Q) and right 0.

From the actual blank root, the machine reaches forward P with empty frame stack and right token Z in exactly 53 primitive steps. All 18 symbolic transitions in [Raw118M2869Macro.lean](Raw118M2869Macro.lean) are literal kernel reductions with arbitrary untouched tails. These include ordinary X/Y transfers, phase-dependent Z, empty/terminal turns, and the two special replacements d::a → s and a with terminal U → s. Each macro has a strictly positive cost.

The finite summaries of the token stacks remember left phase, top frame, parity of special frames, and most recent d/s event; on the right they remember top token, terminal kind, X parity, and first active Y/Z event in each phase. The search begins from the generalized forward P root language with Y immediately after X and #X odd iff trailing V is present. Taking every inverse image under stack pushes (rather than assuming a unique pop) gives a closed relation of 1,181 abstract configurations over 25 left and 93 right valid states. A separate zero sentinel represents invalid stacks.

The actual proof uses the explicit certificate arrays in [Raw118M2869Data.lean](Raw118M2869Data.lean). [Raw118M2869Cert.lean](Raw118M2869Cert.lean) kernel-checks all 26×94 summary pairs against the complete rule implications and checks the frame/terminal metadata. The consumer lifts closure to the real encoded stacks, proves a strictly positive run from every Good configuration, obtains arbitrarily long live blank prefixes by induction, and uses zrun_sound/run_append to prove NeverHalts in the original Machine semantics. The missing F1 transition is never needed. This is a symbolic all-time proof, not extrapolation from the first 53 steps.

## Reproduction and scope

- Discovery: python discover_m2869.py, which prints the certificate arrays. Discovery is not trusted by the formal proof.
- Build order: original Frontier, Symmetry, RootShift, SparseZipper, SweepPumping; then Raw118M2869Data, Raw118M2869Macro, Raw118M2869Cert, Raw118M2869. Use Lean 4.36.0-rc2 and LEAN_PATH for the directory containing the corresponding oleans.
- Original source dependencies were recovered from raw118-wide-3986 artifact 15048626150, matched to the manifest source hashes, and rebuilt locally. The final axiom reports for facts and never are [propext, Quot.sound], with no sorryAx or native_decide.
- Source commit 65ece84c29903edfee4204ad3a34f1c1fac1594d contains the theorem; the exact four tracked source blob hashes are b18994b0a99c03c576c0f1cb54b5c6d10a6b3c0a (data), 3c971fe40289d2e761f1e217169e1f4917913df6 (macro), 71ac9e234160e7834312c7544fcd5818524c5f96 (cert), 4a95446ceaf334bb06bc555aa05c07fcbc860b33 (consumer). The maintainer's full parent source audit remains separate.

See [the Raw118 parent dossier](../agent16-raw118/README.md) for weighted coverage, the long halter (score 756496), exact partition, and integration. Previously proved local macro leaves are retained in the same directory; they must be consumed by their exact parent leaf adapters.
