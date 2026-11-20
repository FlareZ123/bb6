# Agent 8: independent wrapper audit for the 44-class inverse trees

I checked the exact signature of `SheepEvenReachInverse.blank_even_inverse_cases`, its implementation through `reach_last_edge` and `SheepEvenSourceAlgebra.original_even_edge_inverse_cases`, and the affine identities in `INVERSE-TREE-44-CLASSES.md`.

## The wrapper applies uniformly

The theorem accepts
`hy : SheepEven.EvenReach 10 y`,
`hnot : y ≠ 10`,
and
`hpower : d*y+c=2^n`,
and returns either the generic source predecessor equation or the exceptional source predecessor equation, together with a genuine reachable predecessor (x). There is no requirement that (y) itself be a power or that (d,c) be coprime.

The three applications are exactly:
- root (Y_0=2^{1458t}): (d=1,c=0,n=1458t);
- (Y_2=(2^{1458t+10}-9772)/19683): (d=19683,c=9772,n=1458t+10);
- (Y_4=(2^{1458t+12}-179056)/72171): (d=72171,c=179056,n=1458t+12).

The intermediate identities are (19683Y_2+9772=2^{1458t+10}) and (72171Y_4+179056=2^{1458t+12}). Both offsets are nonnegative (c=-B), so the negative-offset natural-number wrapper is the right interface; no Int workaround or sign split is needed.

## Hidden-length bound and exact equations

In either disjunct, the wrapper returns (Y=1+3^h u) with (u) odd. Thus (uge1), (Y-1=3^h u>0), and automatically (hle v_3(Y-1)). Exact equality (h=v_3(Y-1)) is not needed.

For each intermediate node the certificate gives (v_3(Y_i-1)=0), so any returned predecessor must have (h=0). Substituting (h=0) into the wrapper's generic equation gives
[
d(2^{a+1}+1)v+d(2a-1)+2c=2^{n+1}.
]
For (Y_2), the constant term is (39366a-139); for (Y_4), it is (144342a+285941). These match the two intermediate generic equations in the dossier.

The exceptional equation at (h=0) becomes
[
3d,2^a+d(a+3)+c=2^n.
]
This matches the certificate's exceptional (L(a)) expressions (d(a+2)+(d+c)). Therefore both generic and exceptional predecessor types are covered at each intermediate node; it would be unsound to exclude only the generic type.

At the root, (t) is not divisible by 3 for all 44 residue classes (each base residue is nonzero mod 3 and (T_2) is divisible by 3). Hence (v_3(1458t)=6), and LTE gives (v_3(2^{1458t}-1)=7). The wrapper's (h) is therefore in (0,ldots,7), exactly the root range classified by the checker.

## Reachability, positivity and remaining proof obligations

- If `hy` is assumed, `even_reach_preserves_even` proves (y) even from the even origin 10; `blank_even_inverse_cases` also proves the last parent (x) is genuinely reachable and even before applying the original-source splitter. No separate evenness hypothesis is missing.
- The root values exceed 10 since every listed (tge8). The candidate intermediate values are claimed in the arithmetic dossier to be integral, even, and (>10); the Lean development must prove the divisibility/affine identity and (Y_i>10) for every (k), so that `hnot` is available. If reachability is assumed, evenness follows from the wrapper's own path lemma; it need not be proved as a separate premise.
- The valuation claim (v_3(Y_i-1)=0) must be established from the exact congruence modulo (3) (or the stronger frozen modulus) after the affine identity is available. This forces (h=0).
- The terminal-node argument must rule out **both** returned disjuncts for every (a): finite low-(a) modular rows, generic high-(a) signed-power gap, and the exceptional cutoff/divisibility-or-size split. The existing cutoff table is intended to do this; the checker and all 180 modular rows remain unexecuted/unformalized here.

Thus I found no wrapper-interface or source-quantifier defect in the proposed two-node composition. This is a static theorem-shape/algebra review only: I did not run the Python checker or compile Lean, and the 44-class result must remain intermediate until the arithmetic certificate is independently reproduced and the exact original-source Lean closure passes with an exported axiom audit.

— Agent 8
