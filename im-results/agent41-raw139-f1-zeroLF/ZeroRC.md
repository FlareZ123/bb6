# Raw139 F/1 = 0RC — source-certified exhaustive closure

Literal partial table `[7,24,11,24,14,21,3,16,12,11,24,9]`. Certified theorem `BB6.Agent41F1ZeroRC.all_completions_weighted : ∀ m, compatible parent m → WeightedBound 3807 m`. Original-source Lean 4.36.0-rc2 certification passed with standard axioms only in [run 45607499262](https://github.com/FlareZ123/bb6/actions/runs/45607499262), pinned revision `6d8a67d372e3ce0a01802e3c7eb8b04e01e838f9`, compiled artifact `15018441852`.

Partition: 14 internal splits, 323 terminal leaves, 202 translated cycles, 91 last-hole queries (including 3801 and 1881), 12 FAR, 18 growth proofs.

## New mechanisms
- 14 affine one-block recurrences and one two-block recurrence (H5) are checked for every parameter, using the symbolic-gap interpreter.
- H3 has four-phase recursively nested carry digits with words A=0110, B=0000, C=0111, D=0001. The successor sends empty→C(empty), A(g)→B(g)→C(g)→D(g)→A(next(g)). Its core has costs 25,19,25,19,10+coreCost(g)+8 and leaves its arbitrary left context intact. The outer double sweep increases the repeat parameter by two and applies the successor.
- H7 has an ordinary little-endian binary counter, each digit encoded as 0b. Core cost 5 at empty or leading 0, and 2+coreCost(tail)+2 at leading 1. The stage is reached after 178 steps; every cycle increases the repeat count by one and increments the binary word.
- H8 has an eight-period suffix recurrence. Entry at 1738, repeat count 7, eight suffix phases; each octet costs 432n+2264 and increases n by 8.
- The common outer right/left sweep engine is proved for arbitrary unexamined suffix, rather than re-proved in each phase.

## Reproduce
Run `bash im-results/agent41-raw139-f1-zeroLF/reproduce-zeroRC.sh`. The archive SHA-256 is `e714f0772d6e7df0d64e3da63153c8450e39abead67caf8fb5b61d1241e5dbd8`. The script reuses only `Agent41SymSweep.lean` from the source-accepted 0LF archive and compiles the actual dependency closure. It audits all eighteen nonhalting claims and final theorem against the standard-axiom allowlist. This is a separate exact sibling; no global roster count is claimed yet.
