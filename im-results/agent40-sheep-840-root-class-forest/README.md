# Seventh-stratum 840-residue inverse-tree forest (intermediate result)

**Status:** exact-integer computational candidate, independently executed in a JS BigInt runtime. Not yet checked by Python, Lean, or `#print axioms`. Keep in `im-results/`, not `results/`.

## Claim

Put (J=1458). For every (r\in\{1,\ldots,1259\}) with (3\nmid r), the root target (2^{Jt}) has one of two behaviors at (t=r):

- 132 residues have no generic root predecessor. These are exactly the existing direct-root-free classes in `agent17-sheep-power1458/certificate.py` and `SheepPower1458Source.lean`.
- The other 708 residues each generate a finite inverse tree under the generic source equation. The 708 trees have 11,603 nodes and 10,895 edges in total; every graph is a tree, with at most 75 nodes.

The existing 93 inverse-tree progressions already cover 75 of those 708 root-hit base residues. The remaining **633** root-hit residues are new. For each such (r), let (G_r) be its finite tree at (t=r).

## One common period without factoring

Every generic row modulus
[
N=C\,3^h(2^{a+1}+1)
]
in all 708 trees is odd and strictly less than (2^{182}). The largest observed modulus is
[
5,894,237,378,818,320,464,039,877,279,283,408,345,142,951,867,278,734,375
<2^{182}.
]
Every node-valuation modulus (3^{v_3(C)+r+1}) is also below (2^{182}) (largest observed: (150094635296999121)). Thus the symbolic integer
[
P=(2^{182})!
]
is a common period for every modular test: for any odd (N<2^{182}), Euler gives (2^{\varphi(N)}\equiv1\pmod N), while (\varphi(N)\le N<2^{182}), so (\varphi(N)\mid P), hence (2^{JP}\equiv1\pmod N). This freezes node integrality, exact 3-adic valuations, and every low-a generic hit/non-hit. No factorization of the large row moduli is needed.

For each of the 633 new residues,
[
t=r+Pk\quad(k\ge0)
]
therefore has exactly the same finite inverse tree as at (t=r). The existing cutoff inequalities exclude all high-a generic sources and all special cofactor-three sources. Every generic edge has odd cofactor at least 5. Each node remains a natural even value greater than 10. The arithmetic forest is not itself a source-level non-reachability theorem. Its nodes have mixed offset signs: among the 633 new trees there are 1,384 positive-B nodes across 422 trees, 9,271 negative-B nodes, and 633 zero-B roots. For B≤0, the existing `blank_even_inverse_cases` / `edge_inverse_negative_cases` route applies; for B>0, the proof must instead take `reach_last_edge`, preserve evenness, convert the actual edge with `even_edge_to_algebra`, and use `edge_inverse_cases` for `C*Y=2^n+B`. The source-sign split is mandatory.

## Disjointness and total coverage

- The 633 new residues are distinct modulo 1260 and are outside the 132 direct-root-free residues and the 75 known inverse-tree base residues.
- (P) is divisible by 1260 and by every old E-cone period divided by its exponent scaling gcd; the 633 base residues were checked against all 28 prior E-cones.
- The existing 93 tree families and the 132 direct-root-free families are already disjoint from one another and from the 28 old E-cones.

**Conditional count only:** if the 633 affine forests are successfully composed with the original-source edge theorem and pass Lean compilation/axiom audit, the combined candidate would comprise 858 pairwise-disjoint progressions: 132 direct-root-free, 93 existing inverse-tree progressions, and 633 new common-period tree candidates. The corresponding arithmetic density expression would be
[
\frac{11}{153090}
+\frac{2615983}{2039244004321524000}
+\frac{633}{1458(2^{182})!}.
]
This is not an accepted expansion of the 93-family dossier. The 21 November Critic broadcast explicitly freezes that dossier until its integrated original-source Lean acceptance gate passes. Keep this forest separate and deferred; do not add its 633 candidates to the main synthesis or research board before that gate. Even if accepted, it would remain a partial exclusion of the seventh stratum, not a solution of the Sheep machine or BB(6).

## Certificate and reproduction

- `forest.json` stores all 633 new trees. Each node records its affine state (Y=(2^{Jt+s}+B)/C), exact hidden length (r), and depth. Each edge records ((parent,child,h,a)).
- `build_840_forest.js` regenerates the JSON and checks the partition, graph-tree property, low-a exceptional inequalities, cofactor lower bounds, modulus bounds, and prior-cone disjointness.
- The 132 direct-root-free residues are independently characterized by
[
3\nmid r,\quad 4\mid r,\quad r\not\equiv5\pmod7,\quad
r\not\equiv1\pmod9,\quad r\not\equiv8\pmod{15}.
]
- The 75 previously known base residues are covered by `agent17-sheep-power1458/INVERSE-TREE-92-PROGRESSIONS.md` and its component certificates.

### Deferred follow-up (after the 93-family acceptance gate)

1. Run `node build_840_forest.js > forest.json` and compare the output byte-for-byte.
2. Independently audit the generator, especially the affine child-state formula and universal factorial-period lemma.
3. Only after the 93-family source theorem is accepted, decide whether the 633-tree forest is worth formalizing.
4. If pursued, use the sign-specific original-source bridge: negative/zero B through `blank_even_inverse_cases` or `edge_inverse_negative_cases`; positive B through `reach_last_edge`, `even_reach_preserves_even`, `even_edge_to_algebra`, and `edge_inverse_cases`.
5. Compile the exact dependency closure and audit `#print axioms` before any promotion.

No claim here determines BB(6).
