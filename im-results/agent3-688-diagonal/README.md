# #688 exponential stopping diagonal: proof package

The [main mathematical theorem](../../results/2026-11-24-688-exponential-diagonal-density-agent3.md) gives the exact odd-index stopping condition and density-zero necessary restriction. This package now includes a **complete finite inverse decision for each individual diagonal index**, covering all collapsed arithmetic transitions, including the exceptional and even phases. The unbounded existential over indices remains open.

## Exact inverse cone

Decode `ExactInverse.lean.xz.b64` (base64 then xz); the decompressed Git blob SHA-1 is `669b3b8813dad68c2a91d1ffd81afa3a51645a3d`. Compile it with Lean 4.36.0-rc2. This standalone module implements the same collapsed arithmetic map from section 1 of the main theorem. `parents_iff` checks an exhaustive candidate generator against the forward map: at most eleven candidates, obtained from the six boundary constants and the regular H/L and l=1 formulas. The filter gives soundness even when natural subtraction truncates. Completeness is proved by splitting the genuine forward transition.

For W=2b+c, the rank W²+c strictly increases on every successful forward transition, including the weight-preserving r=1 branch (c strictly increases there). Therefore every target's inverse cone is finite. `exact_decision` proves that finite recursive checking with rank as fuel decides reachability from (0,2), without any assumption about the machine's unknown ultimate behavior. `closedCertificate_sound` gives a more practical proof checker using a hash set of all ancestors, and `proveExcluded_sound` checks a fuel-bounded producer without mistaking a timeout for exclusion. The theorem `j1_excluded` is a kernel-decided exclusion of the first odd stopping index. All six audited declarations use only propext, Classical.choice, Quot.sound. This is a standalone transcription check, not a compiled import of the original upstream file or of the older archived Collapse module.

The finite independent Python exact search `exact_inverse.py` excludes indices 1,3,5,7,9,199,265,1189, with ancestor counts 12,21,15,2596,71,32148,48641,603497, respectively. Unlike the prior large-target sieve it follows every arithmetic predecessor all the way to an empty frontier; the finite runs other than j=1 have not been turned into kernel-accepted closed certificates. An open/capped run is never an exclusion.

## Previous proof package and evidence

Read [the theorem](../../results/2026-11-24-688-exponential-diagonal-density-agent3.md) for the complete mathematical argument. Pinned source: google-deepmind/cryptids@3647718b5df22e1a61462dec0376bd204526285a, BusyBeaver/BB6/M_1RB1RF_1LC1LF_0RE1LD_0LB1LD_HHH1RC_1RA0RD.lean.

Decode proof.tar.xz.b64 to proof.tar.xz (SHA256 a7fdb1646cf7b0f0e42f0825558e4612f80f1802e3b99aa99ea535484ab4e574), extract. With Lean 4.36.0-rc2 and LEAN_PATH=. run in order:
    lean -o Collapse.olean Collapse.lean
    lean -o Phase.olean Phase.lean
    lean -o Root.olean Root.lean
    lean -o Inverse.olean Inverse.lean
    lean -o Ray.olean Ray.lean
    lean -o Coeff.olean Coeff.lean

The six modules compile locally. Key audited declarations: halt_iff, halt_gate, even_parent, odd_step, evenForm_succ, diagonal_terminal_equation, root_halt_iff, odd_large_parent, odd_diagonal_unreachable, root_halt_odd_index, child_correct, child_wrong, collision, coeff_good, coeff_exact. Only propext, Classical.choice, Quot.sound where needed; no sorryAx.

scan_ev.cpp is an experimental exact collapsed recurrence simulator. Compile g++ -O3 -std=c++17 scan_ev.cpp -o scan_ev; run ./scan_ev 1000000000. Result no halt, endpoint b=192039805,c=615914277,W=999993887, 15 even entries (all boundary-5). W=2b+c increments between 0 and 8 per collapsed step, by direct case analysis; hence this run is safe in uint64_t. No raw TM step score is inferred. sieve.py gives the empirical finite congruence counts with exact affine integer arithmetic: at depth 19, 84,441 of 524,288 residues survive (not an independent kernel certificate). The theorem establishes the zero-density limit without using those numbers.

The full upstream import and end-to-end Lean counting proof remain pending. The new inverse decision is exact per target, not a bound on all indices. The next mathematical goal is to prove a uniform exclusion across the unbounded odd-index family, rather than treating finite target closure as a machine decision.
