# B1 synchronizing obstruction is a left-strip digit shift

**Status:** exact finite-automaton property plus an elementary 3-adic digit lemma. This is not an all-time root invariant and does not prove #623 nonhalting.

## Exact B1 transition identity

In `im-results/agent27-623-root-scan/NonSynchronizingSCCs.json`, recurrent component B1 has 30 states and 90 internal transitions. Every state records a previous digit pair `(x_i,y_i)`; every internal outgoing transition has next pair `(x_{i+1},y_{i+1})) with

[
x_{i+1}=y_i.
]

I checked this identity on all 90 listed internal edges (zero exceptions). B1 has projection histogram `2/1`: two L states and one R state at every subset state. Thus it is the L-branch ambiguity component, not a generic unresolved SCC.

## The corresponding exact digit lemma

Let (u_0,ldots,u_N) and (v_0,ldots,v_N) be base-three digits, and put
[
U=sum_{i=0}^N u_i3^i,qquad V=sum_{i=0}^N v_i3^i.
]
Suppose (u_{i+1}=v_i) for every (sle i<t). Then
[
U-3Vequiv
left(sum_{i=0}^{s}u_i3^i
      -3sum_{i=0}^{s-1}v_i3^iight)
pmod{3^{t+1}},
]
and the displayed low-prefix remainder (R_s) satisfies
[
|R_s|<3^{s+1}.
]
The congruence is simply cancellation of the coefficients at positions (s+1,ldots,t); the bound follows because each low prefix is in ([0,3^{s+1})) and ([0,3^s)), respectively.

For the #623 source coordinates used in `RootPhaseInvariant.md),
[
X=2g-gamma_s,qquad Y=6q,
]
so
[
X-3Y=2(g-9q)-gamma_s.
]
Consequently, a B1 run across the central digit interval forces the left predecessor residual (2(g-9q)-gamma_s) to have a representative modulo (3^{t+1}) of absolute value below (3^{s+1}). If the state is a terminal predecessor, the exact cocycle gives (|g-9q|le 23n+140) for (nge10). Since the central modulus is much larger than this strip, the congruence then identifies the actual residual with the low-prefix representative.

This gives a concrete interpretation of B1: its persistent language is exactly the digit-shift cancellation pattern for the left dangerous linear form (g-9q). The remaining task is not to re-prove the SCC fact; it is to show that the actual reset prefix fixes (R_s) outside the terminal interval. The reset label and actual source carry at its start are the data needed to evaluate that low prefix.

## Relation to B2

B2 has the opposite projection histogram `1/2`: one L state and two R states. The exact R affine first-coordinate map is
[
(X,Y)mapsto -4X-3Y+C,
]
and the right predecessor strip is (|4g+9q|le23n+140). Also
[
4X+3Y=2(4g+9q)-4gamma_s.
]
This aligns B2 with the right dangerous linear form, but I have **not** derived an analogous explicit digit recurrence for its 30-state language. Do not treat that analogy as a theorem.

## Next useful proof step

1. Compose the reset label with the actual source carry at the reset start, and compute the exact low-prefix representative (R_s) for B1.
2. Prove this representative cannot lie in the terminal interval under the source-derived correction bounds; this would eliminate the dominant L-ambiguity obstruction without proving global synchronization of all 66 carry states.
3. Derive the corresponding B2 digit transducer for (4X+3Y), retaining the exact threshold branch (gge 3D+2r+c_s).

All material remains intermediate in `im-results/`; no claim about the full root orbit is made.
