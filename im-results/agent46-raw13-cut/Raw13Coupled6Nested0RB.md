# Nested counter family for three coupled6 E1=0RB leaves

Agent 46, 2026-11-27. Mathematical derivation; Lean acceptance pending.

Literal partial tables:
- 1RB1LD1RC0RE1LA1RE1LA0LA0LF0RB1LA---
- 1RB1LD1RC0RF1LA1RE1LA0LA---0RB0LC0RB
- 1RB1LD1RC0RF1LA1RE1LA0LA---0RB0LD0RB

Use the actual SweepPumping zipper notation A(L,R), current symbol first on L, nearest-first words. Set U=11, X=10, Z=00. Each table enters A(empty,U^2 0 U^4 0) after 107 assigned primitive steps. The following common identities apply to all three tables and arbitrary suffixes.

Write B⟨L,W⟩ for state B with L strictly left of head and W starting at head (empty means blank). Its elementary transitions are:
- A(0L,W) -> B⟨1L,W⟩ in one step.
- B⟨L,U W⟩ -> B⟨Z L,W⟩ in two steps.
- B⟨L,0 U W⟩ -> B⟨011 L,W⟩ in three steps, where the last zero of 011 is nearest the head.
- B⟨L,0⟩ -> A(1L,1) in two steps.
- B⟨L,10⟩ -> A(L,10) in three steps.
- A(X L,R) -> A(L,U R) in two steps.
- A(U L,R) -> A(L,01 R) in two steps.

The marker identity is B⟨L,0 U W⟩ -> B⟨011 L,W⟩: B0 writes 1, C1 writes 1, E1 writes 0. These steps and the terminal 10 identity use only assigned transitions.

Inductively pumping the B and A pair identities yields, for m >= 1:
(1) A(0L,U^j 0 U^m 0) -> A(1 0^(2m-1) 11 Z^j 1L,1), in 2j+2m+4 steps.
(2) A(0L,U^j 10) -> A(Z^j 1L,10), in 2j+4 steps.
(3) A(X^j L,R) -> A(L,U^j R), in 2j steps.

Encode little-endian binary digits zero=Z, one=X. Formula (3) followed by (2) increments a counter with fixed right word 10:
 A(X^j Z L,10) -> A(Z^j X L,10), cost 4j+4.
For every bit list of length m, this reaches the all-one list after finitely many increments, by ordinary induction on its natural binary value (each increment adds one and preserves width; no increment is taken from the all-one list).

For m>=2, define M arbitrary. Starting from A(1 0^(2m-1) 11 M,1), one X-pair step yields A(Z^(m-1) 11 M,111). Apply (2) with j=1 (the last right blank is implicit, and the first four steps are identical with/without that explicit zero) to obtain A(Z X Z^(m-2) 11 M,10). This is an m-bit counter of value 2. Fill it to all ones, then use (3) to reach A(11 M,U^m 10). A two-step U-pair removal gives A(M,0 U^(m+1) 0). Thus (1) and this inner counter procedure give
 A(0L,U^j 0 U^m 0) -> A(Z^j 1L,0 U^(m+1) 0)
 by a strictly positive number of assigned steps.

The outer counter has left word enc(bits) 1 and right word 0 U^m 0. For a nonmaximum outer list, its left word is X^j Z L. Apply (3) and the inner procedure with suffix 0L, giving
 A(X^j Z L,0 U^m 0) -> A(Z^j X L,0 U^(m+1) 0).
This increments the outer binary value and increases m by one.

From root(k,m)=A(empty,U^k 0 U^m 0), where m>=2, the first step is unchanged by explicitly padding L with a single blank. Apply the inner procedure to obtain A(Z^k 1,0 U^(m+1) 0). Fill the k-bit outer counter from zero to maximum via exactly 2^k-1 increments; its right parameter is now m+2^k. Then (3) moves the k one pairs to the right. Two assigned steps from A(1,U^k 0 U^(m+2^k) 0) produce root(k+1,m+2^k), since D0 writes one on the blank immediately to the left of the final marker.

Consequently root(k,2^k) -> root(k+1,2^(k+1)) by positive assigned runs for every k>=2. The authentic seed is root(2,4) at time 107. This establishes nonhalting for every compatible completion of each of the three partial tables. No claims about parent coverage or global BB6 exactness follow without integration.

The fourth similar table 1RB1LD1RC0RE1LA1RE1LA0LA0LF0RB0LB--- does not share the terminal 10 identity (it enters B instead of A). It is intentionally excluded.

The symbolic identities were derived with the actual move0 rules; finite concrete replay is only a check of the seed and identities, not a substitute for the arbitrary-width induction.
