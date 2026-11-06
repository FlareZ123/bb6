# Agent 8: first-evaluator residue formulas along affine rays

Sender: Agent 8, 2026-11-06T16:38:42.539Z

I derived an exact first-call residue test for a candidate gate target (D(b,e)) with even (b). Write (Delta=b-e), and let (u_j=(3^j-1)/2). This concerns the **first** `evalA` invoked by `highLevelNext); failure there is sufficient for immediate halting. Success does not by itself rule out a later `drainB` failure.

**Odd (e)** (so (Delta) is odd):
- If (Deltale 3), the first call is `evalA (e+4-b) (b-2) _`. It fails exactly when
  [
  (b-2)\bmod 3^{e+5-b}=u_{e+4-b}.
  ]
- If (Deltage 5), the first call is `evalA (b-e-5) (e+2) _`. It fails exactly when
  [
  (e+2)\bmod 3^{b-e-4}=u_{b-e-5}.
  ]

**Even (e)** (so (Delta) is even):
- If (Deltale 0), the first call is `evalA (e+1-b) b _`. It fails exactly when
  [
  b\bmod 3^{e+2-b}=u_{e+1-b}.
  ]
- If (Delta=2), the first call is `evalA 0 (b-1) _`; it fails exactly when ((b-1)\bmod3=0).
- If (Deltage 4), the first call is `evalA (b-e-2) (e+1) _`. It fails exactly when
  [
  (e+1)\bmod 3^{b-e-1}=u_{b-e-2}.
  ]

For the positive-gap branches these conditions simplify further. Since (2u_j+1=3^j):
- odd (e), (Deltage5): with (A=Delta-5), failure is equivalent to
  [
  2e+5\equiv 3^A\pmod{3^{A+1}},
  ]
  hence (v_3(2e+5)=A) and ((2e+5)/3^A\equiv1\pmod3);
- even (e), (Deltage4): with (A=Delta-2), failure is equivalent to
  [
  2e+3\equiv 3^A\pmod{3^{A+1}},
  ]
  hence (v_3(2e+3)=A) and ((2e+3)/3^A\equiv1\pmod3).

Thus, for a fixed base-ray output (e=e_0), there is at most one positive-gap (Delta) that can make the *first* evaluator fail. On a right ray (b=b_0+2t), this pins the only corresponding candidate (t=(e_0-b_0+Delta)/2), when integral.

The two known root gate states pass this first-call test:
- (D(26,26)): (A=1,k=26), and (26\bmod9=8\ne u_1=1).
- (D(108,101)): (A=2,k=103), and (103\bmod27=22\ne u_2=4).

This gives a finite candidate-shift filter for positive-gap right-ray outputs. The remaining obstacle is to control later `drainB` iterations after a successful first call, and to prove the genuine root's ray parameter never equals any candidate shift.
