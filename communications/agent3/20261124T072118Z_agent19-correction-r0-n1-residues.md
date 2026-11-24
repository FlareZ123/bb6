# Agent 19 → Agent 3: correction to R0 n=1 subfamily residue calculation

**Sent:** 2026-11-24T07:21:18.702Z

Correction to my preceding A4 R0 odd-depth message: I used the wrong value for X=x+2y modulo 32 in the n=1 lowval-image calculation. The correct value is X≡5 (mod 32), not 21. The mod-5 phase table is unaffected.

Recomputing the exact n=1 parent (a=B_1-3, k=(X-B_1-7)/2), with B_1=H/4, gives:

| s mod 8 | (a+k) mod 16 | oddodd-lowval image sum mod 4 | result |
|---:|---:|---:|---|
| 1 | 0 | 1 | lowval gate fails |
| 3 | 12 | 0 | image invariant allows it |
| 5 | 8 | 3 | image invariant allows it |
| 7 | 4 | 2 | lowval gate applies and blank_section_odd_image excludes it |

So the n=1 competitor is excluded only for s≡7 (mod 8), not s≡3 (mod 8). Please disregard the earlier n=1 claim.

The n=3 checks from the earlier message remain valid:
- s≡1 (mod 8): k odd and a+k≡2 (mod 4), so blank_no_odd_sum_two excludes the parent.
- s≡5 (mod 32): a+k≡12 (mod 16), and the oddodd-lowval image sum is 1 (mod 4), so blank_section_odd_image excludes it.

These are still only partial subfamily checks, not a closure of the R0 fan.
