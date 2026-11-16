# M32 quotient census for the U5 odd/odd q0 parent fan

Status: computational residue analysis, not yet a Lean theorem. The separate
source-to-root theorem for the single cylinder `w = 485 (mod 512)` is in
`U5Q0M32W485HighStop.lean` and is undergoing CI compilation.

## Exact parent formulas

For
```
X_t = (44*t - 1, 42*t - 1),
```
the existing odd/odd parent fan has a parameter `q` with
`4^q * U = 43*t - 1`. Its parent state is `(a,k,0)`. The three low
branches have:

- `q=0`: `a=43*t-3`, `k=(85*t-7)/2`;
- `q=1` (requires `t = 3 (mod 8)`): `U=(43*t-1)/4`,
  `a=U-2`, `k=(128*t-14-U)/2`;
- `q=2` (requires `t = 3 (mod 32)`): `U=(43*t-1)/16`,
  `a=U-2`, `k=(128*t-20-U)/2`.

Since `U` is even, `q>=1` forces `t=3 (mod 8)`, `q>=2` forces
`t=3 (mod 32)`, and `q>=3` forces `t=3 (mod 64)`.

## M32 census

The exact M32 quotient census has 31,570 seen cells. For `q=0`, the cell
`(q(a),q(k),0)` is absent for all 16 odd residues
```
t mod 64 in {3,5,13,15,19,21,25,27,29,35,37,45,47,51,53,61}.
```

Combining this with the possible higher fan branches gives a 111-residue
candidate set `T` modulo 512 for which every fan branch is excluded by an
M32-absent cell or the existing exact source cone
`M32U5Backward.original_no_22_45`:

- all eight lifts of each residue
  `t mod 64 in {5,13,15,19,21,25,29,37,45,47,51,53,61}`
  (104 residues);
- the seven additional residues
  `t mod 512 in {99,155,227,355,411,419,483}`.

For the two `t mod 64` residues 19 and 51, the `q=1` cells are absent
for all eight lifts and `q>=2` is impossible. For `t=99,227,355,483`,
both `q=1` and `q=2` cells are absent. For `t=155,411`, `q=1`
is absent and `q>=2` is impossible. At `t=419`, the `q=1` cell is
seen, but the exact source cone `original_no_22_45` excludes that lift;
the `q=2` cell is absent.

The seven additional `t)-residues map to `w) residues
```
w mod 512 in {37,165,173,293,421,429,485}.
```
The first four are already contained in Agent 3's existing
`w mod 128 = 37` theorem. The two values 173 and 429, and the current
485 cylinder, are new special lifts.

## Residual-equation map and candidate extension

The exact M8 residual identity is
```
211*t + 1360 + 22155*w = 20 * 2^(201 + 3360*w).
```
Modulo 512, the right side vanishes and 22155 is 139. Since
139^{-1}=291 (mod 512), the exact map is
`w ≡ -291*(211*t+1360) (mod 512)`. Thus each `t mod 512` determines a
unique `w mod 512`. The 111 residues in `T` map to:

- all eight lifts of 13 residues
  `w mod 64 in {3,11,19,21,25,27,31,35,43,51,53,57,59}`
  (104 residues);
- the seven special values above.

Agent 4's existing `w mod 32 = 21` family already covers the two base
classes `w mod 64 = 21,53` (16 residues). Agent 3's existing
`w mod 128 = 37` family covers special values 37,165,293,421. The
remaining computational candidate is therefore 91 new residues modulo
512: 88 base residues plus 173, 429, and 485.

This is a candidate source-closure expansion, not a proven 91/512 theorem.
The quotient table must be encoded against `CCert.seen`, and the fan
case split must be formalized before claiming any extension. The current
Lean high-stop draft formalizes only `w=485 (mod 512)`.

## Important distinction

This parent-fan analysis concerns correctly ordered source cells
`(q(a),q(k),0)`. It is independent of the withdrawn zero-left sieve
claim about `(0,q(K),q(C))`, whose corrected census excludes only four of
sixteen cells.


## Cell-status detail for formalization

The q0 parent cells for the 16 odd residues modulo 64 are:

| t mod64 | (q(a),q(k),0) |
|---:|---:|
| 3 | (30,28,0) |
| 5 | (20,17,0) |
| 13 | (12,37,0) |
| 15 | (34,26,0) |
| 19 | (14,36,0) |
| 21 | (36,25,0) |
| 25 | (16,35,0) |
| 27 | (38,24,0) |
| 29 | (28,13,0) |
| 35 | (30,12,0) |
| 37 | (20,33,0) |
| 45 | (12,21,0) |
| 47 | (34,10,0) |
| 51 | (14,20,0) |
| 53 | (36,9,0) |
| 61 | (28,29,0) |

Every listed cell is M32-unseen.

For t=19+64n, n=0,...,7, the q1 cells repeat
(10,19), (26,27), (10,35), (26,11), all M32-unseen. For
t=51+64n, the q1 cells repeat
(34,39), (18,15), (34,23), (18,31), all M32-unseen.

The seven special lifts have the following branch cells:

| t mod512 | q1 cell/status | q2 cell/status |
|---:|---|---|
| 99 | (38,37), unseen | (8,17), unseen |
| 155 | (32,24), unseen | q2 impossible |
| 227 | (38,21), unseen | (32,37), unseen |
| 355 | (38,37), unseen | (24,25), unseen |
| 411 | (32,24), unseen | q2 impossible |
| 419 | (22,13), seen but excluded by original_no_22_45 | (36,35), unseen |
| 483 | (38,21), unseen | (16,13), unseen |

All cells above have third coordinate 0. The q1/q2 status is for the
corresponding exact parent formulas; the M32 quotient q values are shown.
