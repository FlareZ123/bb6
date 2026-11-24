# #688 exponential stopping diagonal: proof package

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

No root decision. The actual mathematical result is an exact odd-index stopping criterion and a sparse all-depth restriction. Full upstream import and end-to-end Lean counting proof remain pending.
