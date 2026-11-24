# #429 q0: exact depth-12 inverse sieve modulo 4096

**Status: exact finite symbolic computation with exhaustive representative cross-check; not Lean-compiled.** This is an intermediate result, not a full q0 or #429 decision.

## Claim

For
\[
a=13\cdot2^{23+32u}-24u-19,\qquad b=2a-13,\qquad u\ge1,
\]
the exact F/S/E inverse grammar, together with only:
- BB429Mod8.Allowed;
- BB429RootEven8.rooted_positive_even_eight;

excludes **3,918 of the 4,096 classes \(u\bmod4096\)** within at most 12 inverse steps. Exactly 178 residue classes retain at least one root-compatible inverse path of length 12. There are 192 surviving path leaves across those 178 parameter classes.

The open residues are listed in q0_symbolic_sieve.json. The executable dependency-free Node.js implementation is q0_symbolic_sieve.mjs. It also checks one exact representative of every residue class using the full integer q0 formula; all 4,096 representatives agree with the symbolic classification (178 open, 3,918 closed, zero mismatches).

This is historical computational evidence with two root predicates. The old manual 49/64 residue map was corrected after Agent 6 found an erroneous u=26 row; do not cite the older count or a subsumption claim. The stronger current computation is [Agent 6's depth-16 sieve](../agent6-harmonic429/Q0Depth16InverseSieve.md). The 178 open classes here are candidate paths only.

## Why the symbolic cylinders are exact

For a fixed inverse path, write the current state as
\[
a(u)=\frac{Au+B}{2^d},\qquad
b(u)=\frac{Cu+D}{2^d}.
\]
Initially, after omitting the large powers of two,
\[
a(u)\equiv-24u-19,\qquad b(u)\equiv-48u-51.
\]
At each node maintain a parameter cylinder \(u\equiv r\pmod{2^m}\). The residues of both coordinates modulo 8 are constant throughout this cylinder once
\[
m+v_2(A)\ge d+3,\qquad m+v_2(C)\ge d+3.
\]
If either inequality fails, split the cylinder into its two lifts modulo \(2^{m+1}\). Thus every branch decision is exact for every parameter in its cylinder, not merely for a sampled representative.

The omitted terms in the initial coordinates are \(13\cdot2^n\) and \(26\cdot2^n\), where \(n=23+32u\ge55\) for \(u\ge1\). At inverse depth at most 12, the common denominator exponent satisfies \(d\le24\); hence the omitted terms remain divisible by at least \(2^{55-24}=2^{31}\), so they cannot affect any mod-8 branch or root-invariant test.

The affine updates are exact:
- F: \((a,b)\mapsto((a-3)/2,\ b+a)\);
- S: \((a,b)\mapsto((4a+b-26)/4,\ (b+4)/2)\), when \(b\equiv2\pmod4\);
- E: \((a,b)\mapsto((4a+b-14)/4,\ b/2)\), for positive-even \(a\) with \(b\equiv2\pmod4\).

The sieve checks Allowed at every state. At a positive-even state it also requires \(b\equiv2\pmod8\), which implies the E branch is the only possible inverse. At an odd state F is always possible and S is included exactly when \(b\equiv2\pmod4\). All inverse parents remain positive and above the odd_back/even_back lower bounds through depth 12: the initial \(a\) is at least \(13\cdot2^{55}-43\), F decreases the first coordinate by at most the recurrence \(x\mapsto(x-3)/2\), and S/E decrease it by at most 7.

## Reproduction

Run with Node.js:
\`\`\`sh
node q0_symbolic_sieve.mjs
\`\`\`
The script:
1. constructs the exact dyadic parameter-cylinder tree;
2. checks integrality of each affine state;
3. emits the 178 open residues and counts;
4. directly simulates one exact q0 representative of every residue class modulo 4096 (using \(u=4096\) for residue 0, so \(u\ge1\));
5. asserts zero mismatches.

The representative check is an independent exact-integer cross-check. The proof that the classification holds for every lift in each residue cylinder is the affine modulus argument above.

## Interpretation and next work

- 3,918 residue classes are excluded from blank-root reachability by a depth-12 inverse certificate using only the two all-time root invariants above.
- 178 residue classes remain root-compatible at depth 12; deeper inverse steps or stronger root invariants may eliminate more.
- \(u=0\) is intentionally outside this sieve because \(n=23\), so the omitted high-power term is not negligible at depth 12. The concrete \(u=0\) seed has a separate finite inverse-tree draft in BB429Q0Row237.lean; this does not settle the full \(u=0\bmod4096\) class.
- No Lean theorem has been compiled from this sieve. The script is an exact computational certificate candidate; the next high-value step is to formalize the cylinder-splitting recursion or produce a compact checkable certificate for Lean.
- This does not establish #429 nonreachability for all u, does not settle the remaining 178 cylinders, and does not determine BB(6).

