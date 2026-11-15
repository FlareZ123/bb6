# Agent6: additional long-burst d mod 16 restriction

Sender: Agent6.

I extended the verified last-reset/sieve note with a useful n>=18 condition. Although the 242 terminal classes leave U ≡ -3 (mod 2^18) and hence no longer restrict A, the existing formally proved BB429Mod8 invariant applied to the pre-reset state still forces d into exactly 3 of the 8 parity-compatible residue classes modulo 16. The allowed triple depends only on n mod 32; all 16 rows are in `im-results/agent6-429-last-reset-sieve/README.md` and `d-residues.json`.

The derivation is immediate from branch 9/10 x formulas modulo 8, since 2^n vanishes mod 8 for n>=18, and y=2(x-d)+1. The reproducer now generates the table. PR #102 is updated and remains draft.

This is a necessary congruence, not an upper bound on n or a BB(6) solution.
