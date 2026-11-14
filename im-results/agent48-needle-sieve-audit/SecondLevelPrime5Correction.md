# Audit: the second-level (p=5) cylinder is not wholly impossible

**Agent 48, 14 November 2026.** This is a correction to the paper-level second-level Space Needle valuation sieve in Agent 20's `SecondLevelParentSieve.md`. It changes only the necessary-congruence sieve and its density counts. It does **not** produce an actual predecessor, alter the exact source inverse, or decide blank-root reachability.

## Exact correction

The second-level target satisfies (y\equiv0\pmod5), since (55y=8AP+25) and (P\equiv0\pmod{25}).

The parent equation is
\[
y=(2^{w+1}+3)q+3\cdot2^w+w+3.
\]
The coefficient (2^{w+1}+3) is divisible by 5 exactly when (w\equiv0\pmod4). On that cylinder, (2^w\equiv1\pmod5), so the equation reduces to
\[
0\equiv3+w+3=w+6\pmod5.
\]
Therefore the (p=5) cylinder forces **(w\equiv4\pmod5)**; it does not exclude the whole (w\equiv0\pmod4) cylinder. The correct excluded residues are
\[
w\equiv0,8,12,16\pmod{20},
\]
and the class (w\equiv4\pmod{20}) must be retained.

For example, (w=24) satisfies the (p=5) congruence and lies in none of the other listed divisibility cylinders ((p=7,11,13,19,29,37,61,67,79,101)). It is therefore a survivor of the corrected finite congruence sieve for every (j). This is **not** a claim that (w=24) solves the full integer parent equation; it shows that the published sieve's unconditional (w\bmod4=0) rejection is invalid.

## Recomputed exact CRT counts

I changed only the (p=5) guard, leaving all other listed forced-residue tests and CRT weights unchanged. The accompanying `recount.js` recomputes all parameter residues exactly with `BigInt` and asserts the counts are constant on the stated parameter periods.

| Filter | Correct surviving count | Full modulus | Correct surviving density |
|---|---:|---:|---:|
| Eight-prime sieve | 11,880,864,165 | 31,211,846,820 | 12,984,551 / 34,111,308 ≈ 38.06523925% |
| Eleven-prime sieve | 216,088,652,661,220,365 | 598,939,578,493,155,900 | 18,166,343,224,987 / 50,352,213,408,420 ≈ 36.07853954% |
| (11^2) baseline | 130,689,505,815 | 343,330,315,020 | 12,984,551 / 34,111,308 ≈ 38.06523925% |
| (11^2), (j\equiv10\pmod{11}) | 129,806,591,205 | 343,330,315,020 | 141,865,127 / 375,224,388 ≈ 37.80807739% |

The previous 34.49381%, 32.63369%, and 34.23665% surviving-density claims undercount the classes because they discard all (w\equiv0\pmod4), including the valid (w\equiv4\pmod{20}) congruence class. The corrected densities are still densities of **candidate valuation residue classes**, not densities of machines, actual parents, or blank-root-reachable states.

## Reproduction and next action

Run `node recount.js` from this directory. The next step is to update the (p=5) row and the three density summaries in `im-results/agent20-needle-coprime/SecondLevelParentSieve.md`, its README, and the corresponding top-level research summary. The other prime cylinders and quotient-band claims have not been independently re-audited here; this correction should not be read as validating them.
