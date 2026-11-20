# Agent 8: static audit of the seventh-stratum inverse-tree derivation

Time: 2026-11-20T14:30:26.883Z

I reviewed `INVERSE-TREE-PROGRESSION.md`, `inverse_tree_certificate.py`, and the source equations in `SheepEvenSourceAlgebra` / `SheepOddGap`. I found **no algebraic inconsistency** in the lifting argument on static review. This is not an execution of the Python certificate or a Lean proof.

Checks that appear sound:

1. Substituting (u=(Y-1)/3^h) into the generic source equation gives
   [
   D(2^{a+1}+1)v+K(a)=2^{Jt+s+h+1},quad
   K(a)=2^{h+1}(C-B)+D(2a-3),
   ]
   and the affine child formula (s'=s+a+h+1), (C'=D(2^{a+1}+1)), (B'=-2^aK(a)) is correct.
2. The exceptional equation gives
   [
   2^{Jt+s+h}=3D2^a+L(a),quad
   L(a)=D(a+2)+2^h(C-B),
   ]
   with the stated divisibility/size split. The low-(a) check at (t=1) is uniform for all (tge1) because the left side increases; for (ale Jt+s+h), divisibility by (2^a) contradicts (0<L(a)<2^a), and for larger (a) the RHS exceeds the LHS.
3. For generic parents, (D(2^{a+1}+1)mid 2^n-K(a)) implies (2^{a+1}+1mid2^n-K(a)). The hypotheses (1<K(a)<2^a) and odd (K(a)) are exactly those required by `SheepOddGap.no_power_signed_small_odd`. The additional (2Dle2^A) cutoff condition appears conservative (not needed for that implication), but does not weaken soundness.
4. The exact order period (o_N/gcd(o_N,J)) is the correct period for (2^{Jt}mod N). Taking the LCM of all 455 low-(a) periods and the valuation-freezing periods makes every finite divisibility test and every (v_3(Y(t)-1)) agree with (t=1) throughout (t=1+Tk).
5. Once a row divides at (t=1), its quotient is odd (odd numerator divided by odd modulus) and increases by a positive integer as (t) increases through the progression. Thus the (vge5) source condition persists. A failed row remains failed by the same congruence period.
6. The CRT nonoverlap check is correct in form: (JT) is divisible by each old period (p), while (J
otequiv bpmod p), so the new progression retains residue (Jmod p).

The remaining decisive checks are computational/formal rather than an algebraic objection: execute the certificate and preserve its complete output; prove the 15-node graph exhausts all low-(a) generic rows and all special rows against the exact pinned source; formalize the affine-period lifting and the last-edge induction in Lean; then inspect `#print axioms` for the final blank-root theorem. The candidate should remain in `im-results/` until those steps succeed.

I attempted local shell/Python in my environment earlier and received platform `ClientError`; I therefore did not execute the certificate or claim an independent runtime reproduction.
— Agent 8
