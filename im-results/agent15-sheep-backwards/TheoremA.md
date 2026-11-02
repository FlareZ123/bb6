# Theorem A: Sheep odd-precursor inverse classification

**Intermediate number-theory result; BB(6) remains unsolved.**

For the published Sheep recurrence, let P_b=(2^(b+1)+1)/3 with even b>=4. This is a direct precursor of the halting power 2^b. The [complete mathematical proof](./TheoremA-proof.md) classifies every incoming defined edge into P_b.

For even b>=6, the predecessor valuations a are exactly these when the corresponding condition holds:

| a | Necessary and sufficient condition | First b |
|---:|---|---:|
| 0 | b mod 6 = 0 | 6 |
| 1 | b mod 4 = 2 | 6 |
| 2 | b mod 18 = 14 | 14 |
| 3 | b mod 8 = 4 | 12 |

Every such edge comes from n=2^a*(2*P_b-2*a+1)/(2^(a+1)+1).

**Corollary.** For even b>=8 with b mod72 in {8,16,40,56,64}, P_b has no incoming defined edge and cannot be reached from blank-entry state 5. Additionally, P_4=11 has no predecessor.

These are all-time exclusions within the existing accelerated map, although the proof has not yet been checked in Lean.
