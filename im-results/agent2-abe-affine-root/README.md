# Certified A/B/E affine block framework for Cryptid D

**Current scope.** A locally Lean-checked source-connected extension of Agent32's protected B/E front checker to A, and a generic finite-graph source-soundness/ternary block-lift theorem. The actual finite graph and blank-origin block computations are not yet kernel-certified. Experimental GMP computation reaches 20,000,000 section returns from I_9 without a detected halt or uncovered edge. No all-time D decision, BB(6) value, or improved BB(6) bound follows.

## Mathematical mechanism

Use the original Agent31 Boundary machine and Agent32 padding semantics. A section is `sect n v`, F on blank with blank left, n ones, delimiter 0, and finite tail v. For the A residue n=3k+3, the existing exact prefix reaches A on zero with left 0(10)^(4k+3)11. Consume a word of 10/111 tokens (increments 1/4 to the pair count; primitive costs 2/6m+41 at current pair count m). These identities were already known from Agent35; here we derive them directly using Boundary.reverse_run and scan_run to keep the source closure small. The rest of the front is interpreted with an explicit 3+token-increment pairs, protected by safeRun. A checked B/D-on-zero endpoint with p explicit pairs gives a universal final sweep over 4k+p pairs. Padding witnesses reconcile canonical suffixes with implicit blank cells.

ABEReturn.lean: `a_valid_return` proves the full counted source return for every k, given only a finite ACert validity check. The output n'=8k+2p+3+lead is affine. This complements Agent32's already-certified B/E valid_return. ABEGraph.lean: `edge_sound`, `advance_sound`, `path_sound` compose these exact source returns for any validated finite indexed graph, and `path_shift` proves that a successful L-edge path (n,i)→(m,j) lifts from n+3^L*d to m+8^L*d, with unchanged suffix indices, for all natural d. The statement is not restricted to regular-language suffixes or B/E words.

Lean 4.36.0-rc2 local compilation succeeded. All three audited graph theorems and a_valid_return depend only on [propext, Quot.sound]; no sorryAx/native_decide. Local Boundary is the exact checksum-verified original; RouteFront is from Agent32's route-proof bundle; local Generic and the required BoundaryPadding declarations were reconstructed from the repository. Reproduction against the complete original files uses reproduce.sh.

## Experimental accelerator

root-universal.cpp uses GMP exact arithmetic, cached finite protected-front evaluation with a nonempty-left guard before every nonterminal step, and the recursive affine block lift. For L=block length, split n=x+3^L*q, recurse on x (choose x>=3^L if a positive quotient permits), then add 8^L*q. For an early stop after i returns add 3^(L-i)*8^i*q. Every tested input uses three protected base pairs; the A code preparse can increase the explicit pair count. A finite front that leaves the guard is unresolved, not silently accepted. This model does not yet have a certified concrete table or root path.

The 20-million run from I_9 completed in 4.68s of measured scan time on this local runtime (20,000,000 returns, 28,300,754-bit exact unary parameter, residue 13 mod 27, empty suffix, 317 cached input suffixes including the crosschecks, max suffix length 37). Distinct block decompositions agreed exactly on the four unary seeds through 20,000 returns each; the stricter protected variant's full 20-million checkpoint also matched the earlier variable-buffer implementation. Endpoint text SHA256 b0a2269d983f45e4374c5f284078cf515e3c88d94e6aae943efe2a7c78855047. This is model evidence, not a proof of blank-source nonhalting for the interval.

## Next proof gate

Extract the finite front certificates of the actual graph into Lean; validate them with kernel decision; certify recursive block evaluation and link the genuine blank36 prefix to a successful root path. This can replace long chains of individually specialized DRegular reentry proofs. If an actual terminal branch is encountered, certify its exact source behavior and compose the root path. The existing trillion-cylinder result remains a prepared-state theorem; no cylinder entry is known here.

## Reproduce

The source bundle is `abe-stage1.tar.xz.b64`, decoded SHA256 2ab21be1a676a9bd01bdaabfde335cfc8c890c8f8d63fa5b6c5a6783132667e8. Run `bash reproduce.sh` with Lean 4.36.0-rc2 on PATH; to run the optional C++ experiment, pass a destination directory and compile its root-universal.cpp with g++ -O3 and -lgmpxx -lgmp. The C++ checkpoint path currently assumes /tmp/droute exists.
