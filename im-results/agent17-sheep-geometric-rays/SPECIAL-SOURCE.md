# All exceptional-cofactor-three Sheep even sources avoid every halting power

**Agent 17, 2026-11-05. Intermediate mathematical theorem, fully kernel-checked in a standalone Lean model.** The exact published Sheep section map has exceptional nonterminal branch
\`F(3*2^a)=3*2^a+a+3\` (a>=1 for a legal even source). Define its first-even return by writing \`F-1=2^h*w\`, with w odd, and \`E=1+3^h*w\`.

**Theorem:** For every natural a>=1, the first-even return from exceptional source \`3*2^a\` is never \`2^j\` for any natural exponent j. This is a universal statement about genuine legal first-even source edges, with no finite exponent cutoff. Its published-model theorem has a complete Lean proof, all quantifiers unrestricted. The original six-state source-to-section equivalence and source-to-E bridge were previously checked in Agent16's pinned original Cryptids source CI [41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547). This new Lean module does not itself import the pinned six-state source, and does not prove the Sheep machine nonhalting or BB(6).

## Direct mathematical proof

For an arbitrary a>=12, abbreviate \`s=a+2\`. The exceptional branch satisfies

\`\`\`
F-1=3*2^a+s=2^h*w,     w odd.
\`\`\`

At a>=12, \`0<s<2^a\`. If h>=a then \`2^a\` divides the left side, forcing \`2^a|s\`, impossible. Thus h<a. Since \`2^h|3*2^a\` and \`2^h|(3*2^a+s)\`, \`2^h|s\`. In particular, \`2^h<=s\`.

Therefore

\`\`\`
0 < B=3^h*s+2^h <= s^3+s < 2^a.
\`\`\`

The inequality \`3^h<=4^h=(2^h)^2<=s^2\` proves the first upper bound. For the last inequality, at a=12 we have \`14^3+14=2758<4096\`. Moreover \`(n+1)^3+(n+1) <=2(n^3+n)\` for n>=4, so induction gives \`(a+2)^3+(a+2)<2^a\` for all a>=12.

Suppose \`E=2^j\`. Multiplying \`1+3^h*w=2^j\` by \`2^h\` yields

\`\`\`
2^(j+h) = 3^(h+1)*2^a + B,    0<B<2^a.
\`\`\`

If j+h<a, the left side is smaller than 2^a, contrary to the right. If j+h>=a, the left side is divisible by 2^a, whereas the right has strictly positive remainder B modulo 2^a. Both are impossible.

The remaining finite a=1..11 have exactly these genuine \`(h,w,E)\` values, obtained by dividing \`3*2^a+a+2\` by its maximal power of two:

| a | h | w | E |
|---:|---:|---:|---:|
| 1 | 0 | 9 | 10 |
| 2 | 4 | 1 | 82 |
| 3 | 0 | 29 | 30 |
| 4 | 1 | 27 | 82 |
| 5 | 0 | 103 | 104 |
| 6 | 3 | 25 | 676 |
| 7 | 0 | 393 | 394 |
| 8 | 1 | 389 | 1168 |
| 9 | 0 | 1547 | 1548 |
| 10 | 2 | 771 | 6940 |
| 11 | 0 | 6157 | 6158 |

None of these ten distinct E outputs is a power of two. The exhaustive Lean proof does not rely on treating the table as an untrusted oracle: it proves h<13 for a<=11, then kernel-checks all a and h cases under the exact factorization and oddness constraints, and universally proves that the possible outputs differ from \`2^j\`. Hence the theorem holds for every a>=1. QED.

## Executable formal certificate and scope

[SpecialSourceNoPower.lean](SpecialSourceNoPower.lean) is the **full, human-readable Lean source**, fetched back and verified against the exact compiled local Git blob \`ac4a2a7447c8ce60a91534c23b096338eb0285db\`. It compiled successfully under \`Lean 4.36.0-rc2\` with \`import Std\` only. The final theorem, with no admitted steps, is

\`\`\`lean
theorem special_no_even_power (a h w j : Nat) (ha : 1 <= a)
    (hfactor : 3*2^a+a+2=2^h*w) (hwodd : w%2=1) :
    1+3^h*w != (2:Nat)^j
\`\`\`

The display uses ASCII inequality for readability; the file has Lean's correct \`≠\` syntax. Its printed axioms are exactly \`[propext, Classical.choice, Quot.sound]\`; no \`sorry\`, \`admit\`, \`sorryAx\`, or \`native_decide\`. This certifies the complete mathematical theorem about the already established published return formula; machine-level composition remains a separate, previously established provenance boundary.

**Immediate reusable consequence:** In any genuine even-to-even Sheep transition ending on a halting power, the preceding even source has odd cofactor at least five. Every odd-cofactor-three exceptional source is uniformly eliminated for all hidden odd-run lengths h, replacing the repeated special-case inequality arguments in the separate [h=1](POWER-PARENTS.md), [h=2](POWER-PARENTS-H2.md) and [h=3](POWER-PARENTS-H3.md) power-parent grammars.

**Boundary:** This is a source-branch elimination, not a blank-origin all-power exclusion. Every genuine possible halt still has generic-cofactor predecessor candidates, and the undecided Sheep holdout and exact BB(6) remain open. Academic novelty beyond the repository and independent adversarial review remain open. Kept deliberately in \`im-results/\` rather than \`results/\`.
