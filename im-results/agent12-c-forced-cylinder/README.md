# Computable dyadic cylinders for Machine C

## Result and status

The existing four-sector inverse filter is unchanged. The new theorem shows that its rejected set admits a computable infinite rectangular cylinder at every rejected point. If d(x,y) counts two bits for each odd-low/even-seven step and one bit for each even-affine/six-even-right step, put B=16*2^d. For every rejected (x,y) and every natural u,v, the filter rejects (x+B*u,y+B*v).

The proof is induction on x+2*y, propagating positive shifts through exact inverse maps. The two-bit maps send the shift coefficients to (2u+2v,u+3v); the one-bit maps send them to (2u+2v,v). All active gates persist under positive multiples of 16; at a rejected terminal, the forbidden parity and sum residue persist. No finite depth bound is assumed.

ForcedParameterLift.lean specializes this result to the exact stopping equations:
- Every rejected high (j,m) supplies an entire arithmetic progression j+B*u at fixed m.
- If d+4 <= 2*m+2, the high rejection lifts simultaneously in both j and m by B.
- If d+4 <= 2*m+3, a rejected low m lifts by B.

The saturation hypotheses ensure the exponential terms are divisible by B. Natural-number subtraction is justified by monotonicity and the exact addition identities.

## Verification and scope

The general arithmetic theorem and all three parameter theorems compiled locally with Lean 4.36.0-rc2 (b35cb10cf2ce), against a verbatim reproduction of the four-sector arithmetic definitions, without axioms beyond propext, Classical.choice and Quot.sound. The committed module imports the original FullForcedFilter and includes its source-reachability corollary; full original-source compilation is pending. These are structural statements about an existing filter, not an independent exclusion beyond it, and not a proof of nonhalting of Machine C or an upper bound for BB(6).

The previous point-specific m=0 lift proofs remain valid. The next use is to replace their manually repeated symbolic calculations with generic certificates, then study the nonexcluded inverse sectors instead of merely enlarging finite scans.
