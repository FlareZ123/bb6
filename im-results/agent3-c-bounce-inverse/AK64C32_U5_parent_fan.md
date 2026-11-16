# U5 q=0 parent-fan filters in the mixed A/K64,C32 quotient

**Status:** computational exploration only. The mixed quotient has not yet been given a kernel-checked reachable-state certificate. None of the w=45, w=101, or deeper cylinders below is a source-verified BB(6) theorem. The purpose of this note is to preserve the exact arithmetic and finite-state cells for Agent 32's certificate work.

## Quotient and census

Use
- qA(x)=x for x<2, otherwise 2+(x-2) mod64;
- qK(x)=x for x<2, otherwise 2+(x-2) mod64;
- qC(x)=x for x<4, otherwise 4+(x-4) mod32.

The representative sets are {x} below the thresholds and {x,x+64} for A/K or {x,x+32} for C above them. Apply the exact C-line transition to every representative triple and include every resulting quotient successor. The state space has 66×66×36=156,816 states. The independent BFS reproduces 77,020 reachable abstract states and 576,340 representative edges, matching Agent 32's saved census.

For the U5 q=0 odd/odd target X_t=(44t−1,42t−1), put t=123+168z. The exact source-parent fan is
```
43t−1 = 4^d U,
U ≥ 4 and U even,
a = U−2,
2k+U+6d = 128t−8,
a < 2k.
```
A parent is excluded if its quotient cell (qA(a),qK(k),0) is absent from the mixed quotient's seen set.

## Two short cylinders

### z≡20 (mod32), hence w≡45 (mod128)

Here B=661+903z is odd, so d≥2 is impossible. The only parent cells are:
- d=0: (6,56,0), absent;
- d=1: (64,24,0) or (64,56,0), absent according to z mod64.

A smaller quotient already suffices for this cylinder: A/K exact below2 modulo32 and C exact below4 modulo32. Its state space is 41,616, with 21,190 reachable states and 155,094 representative edges; it excludes d=0 cell (6,24,0) and d=1 cell (32,24,0) for both z mod64 lifts.

The residual identity gives t≡16+23w (mod128); z≡20 (mod32) is equivalent to t≡27 (mod128), hence w≡45 (mod128).

### z≡17 (mod64), hence w≡101 (mod128)

Write z=17+64u. Then
```
661+903z = 4(4003+14448u),
```
with odd bracket, so d≥3 is impossible. The mixed quotient parent cells are:
- d=0: (30,12,0), absent;
- d=1: (22,45,0), absent;
- d=2, u mod4 = 0,1,2,3: (4,19,0), (36,35,0), (4,51,0), (36,3,0), all absent.

The four d=2 lifts are required: the A/K64 projection at depth2 depends on z mod256, not merely mod128. The residual identity gives t≡35 (mod128), hence w≡101 (mod128).

## Sixteen bounded cylinders inside z≡125 (mod128)

For each candidate representative z0, define
```
e = v2(661+903 z0),
dmax = floor((e+2)/2),
k = max(e+1, 2*dmax+4).
```
If e is fixed by z mod2^k and all parent cells through dmax are fixed, then the entire cylinder z≡z0 (mod2^k) has the same parent-fan exclusion. The depth-d A/K64 parent projection depends only on z mod2^(2d+4); the condition k≥2*dmax+4 fixes every such projection. Since k≥e+1, it also fixes e and hence the maximum possible d. Thus the finite cell check proves a whole arithmetic cylinder, conditional on quotient soundness.

The 16 minimal cylinders found are:

| z residue | modulus | e | dmax | w residue | w modulus | Parent cells (d=0 upward; every cell absent) |
|---:|---:|---:|---:|---:|---:|---|
| 637 | 4096 | 7 | 4 | 2053 | 32768 | (62,60), (62,57), (62,22), (46,27), (10,10) |
| 1661 | 4096 | 7 | 4 | 26629 | 32768 | (62,60), (62,57), (62,22), (46,27), (42,26) |
| 2685 | 4096 | 7 | 4 | 18437 | 32768 | (62,60), (62,57), (62,22), (46,27), (10,42) |
| 3709 | 4096 | 7 | 4 | 10245 | 32768 | (62,60), (62,57), (62,22), (46,27), (42,58) |
| 765 | 16384 | 8 | 5 | 119813 | 131072 | (62,60), (62,57), (62,54), (30,35), (38,60), (24,32) |
| 1533 | 16384 | 9 | 5 | 39941 | 131072 | (62,60), (62,57), (62,54), (62,19), (14,40), (2,11) |
| 1789 | 16384 | 8 | 5 | 13317 | 131072 | (62,60), (62,57), (62,54), (30,35), (6,12), (16,4) |
| 3581 | 16384 | 9 | 5 | 89093 | 131072 | (62,60), (62,57), (62,54), (62,19), (14,8), (50,19) |
| 5629 | 16384 | 9 | 5 | 7173 | 131072 | (62,60), (62,57), (62,54), (62,19), (14,40), (34,27) |
| 7677 | 16384 | 9 | 5 | 56325 | 131072 | (62,60), (62,57), (62,54), (62,19), (14,8), (18,35) |
| 8957 | 16384 | 8 | 5 | 54277 | 131072 | (62,60), (62,57), (62,54), (30,35), (38,60), (24,64) |
| 9725 | 16384 | 9 | 5 | 105477 | 131072 | (62,60), (62,57), (62,54), (62,19), (14,40), (2,43) |
| 9981 | 16384 | 8 | 5 | 78853 | 131072 | (62,60), (62,57), (62,54), (30,35), (6,12), (16,36) |
| 11773 | 16384 | 9 | 5 | 23557 | 131072 | (62,60), (62,57), (62,54), (62,19), (14,8), (50,51) |
| 13821 | 16384 | 9 | 5 | 72709 | 131072 | (62,60), (62,57), (62,54), (62,19), (14,40), (34,59) |
| 15869 | 16384 | 9 | 5 | 121861 | 131072 | (62,60), (62,57), (62,54), (62,19), (14,8), (18,3) |

The w residues follow from t=123+168z and the uniform residual congruence 211t+1360+22155w≡0 modulo the relevant power of 2. Every listed w class is inside w≡5 (mod128). These cylinders are pairwise disjoint from the short w=45 and w=101 cylinders.

## Next proof obligations

1. Agent 32 should reproduce the listed cells from the saved mixed quotient script and certify the exact quotient closure in Lean (or identify a smaller quotient/certificate).
2. Prove the representative-transition simulation lemma for qA/qK/qC in Lean, including all threshold-crossing cases.
3. Once the quotient's seen-set certificate is kernel checked, add the finite parent-fan case analysis and lift each z cylinder to its w residue using the residual congruence.
4. Only then compose with the existing U5 residual y=3, B_s, A_s, and high m=0 pullback chain.

Do not cite this note as a formal result before those steps pass.
