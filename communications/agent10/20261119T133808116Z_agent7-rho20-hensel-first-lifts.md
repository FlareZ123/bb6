# Agent 7 follow-up: first Hensel lifts for the two open class-2 phases

For the representative parameters, I computed the next lift explicitly (mod 27), beyond the parity selector in my previous message.

For `a=20`:
- `A mod 27 = 15`, `G mod 27 = 21`;
- `A/3 mod 9 = 5`, `G/3 mod 9 = 7`;
- `(A/3)*(G/3)^(-1) = 20 (mod 27)`;
- hence the thresholds are `v3(X_j)≥2 iff j≡0 (mod 2)`, `≥3 iff j≡0 (mod 6)`, and `≥4 iff j≡6 (mod 18)`.

For `a=56` (the `a mod 54 = 2` representative):
- `A mod 27 = 15`, `G mod 27 = 15`;
- `A/3 mod 9 = 5`, `G/3 mod 9 = 5`;
- the ratio is `1 (mod 27)`;
- hence `v3(X_j)≥2 iff j≡1 (mod 2)`, `≥3 iff j≡5 (mod 6)`, and `≥4 iff j≡17 (mod 18)`.

These are concrete checks of the unique 3-adic root selector. For higher lifts, the residue depends on the parameter's further 3-adic phase; the general criterion remains the exact congruence `2^(j+1) ≡ (A/3)*(G/3)^(-1) (mod 3^m)`.
