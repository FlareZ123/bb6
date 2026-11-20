# E/B/P2 packet index cocycle

Status: **exact arithmetic synthesis of existing source-macro shapes; not a global source-closure theorem**.

This note records the common affine index dynamics behind the E packet, B packet, and P2-reset source lemmas. It is intended to help classify root-reachable residue cylinders and identify the remaining marker/resource obligations. It does not claim that every natural-number orbit terminates.

## 1. Macro shapes and index transitions

Use the packet notation and source theorems in `PacketSource.lean` and `PacketP2ResetSource.lean`.

### E packet

The source macro has the shape
[
E(k,q,p+3;Y)longrightarrow E/B/A	ext{ packet }(8k+9,q+2,p;Y).
]
The suffix (Y) is unchanged. Re-express the output prefix (8k+9) according to (k\bmod 3):

| Input residue | Output class | New index | Exact cocycle |
|---|---|---|---|
| (k\equiv0) | A terminal | — | — |
| (k\equiv1) | B, since (8k+9=3b+2) | (b=(8k+7)/3) | (5b+7=8(5k+7)/3) |
| (k\equiv2) | E, since (8k+9=3e+4) | (e=(8k+5)/3) | (e+1=8(k+1)/3) |

Each E packet call changes ((q,p)) to ((q+2,p-3)), so (q+p) decreases by exactly one.

### B packet

The B source macro has the shape
[
B(k,q+1,p;Y)longrightarrow (8k+10,q,p;Y).
]
Again (Y) is unchanged. Re-express the output prefix according to (k\bmod3):

| Input residue | Output class | New index | Exact cocycle |
|---|---|---|---|
| (k\equiv0) | E, since (8k+10=3e+4) | (e=(8k+6)/3) | (5e+6=8(5k+6)/3) |
| (k\equiv1) | A terminal | — | — |
| (k\equiv2) | B, since (8k+10=3b+2) | (b=(8k+8)/3) | (5b+8=8(5k+8)/3) |

Each B packet call changes (q) to (q-1) and leaves (p) unchanged, so (q+p) again decreases by exactly one.

### E,p=2 reset

The fixed-tail P2 source macro has the shape
[
P2(k,Q;\mathrm{fixedTail})longrightarrow
(8k+5,0,2Q+6;\mathrm{MarkerTower}(3)).
]
Its output is:

| Input residue | Output class | New index | Exact cocycle |
|---|---|---|---|
| (k\equiv0) | B with zero q-field | — | terminal B-zero boundary |
| (k\equiv1) | E, since (8k+5=3e+4) | (e=(8k+1)/3) | (5e+1=8(5k+1)/3) |
| (k\equiv2) | A with p congruent 2 | — | terminal A-p2 boundary |

Unlike ordinary E/B packet calls, the P2 reset can increase (q+p): it resets (q=Q) to zero and sets (p=2Q+6). It also changes the suffix to the marker family. A second P2 reset therefore requires a source theorem for the *current marker family*, not merely the same index arithmetic.

The separate `EAltPacketCompose.e_two_to_zero` source theorem handles a MarkerTower input and changes it to a MarkerZero suffix. This marker mutation is the central obstruction to blindly iterating the fixed-tail reset theorem.

## 2. The common 3-adic cocycle

Every continuing E/B/P2 edge above has the form
[
k'=(8k+c)/3
]
for a branch-specific constant (c). The corresponding integer linear form (L(k)) satisfies
[
L(k')=8L(k)/3.
]

The branch forms are:

| Edge | Required residue | (c) | (L(k)) |
|---|---:|---:|---|
| E→E | (k\equiv2) | 5 | (k+1) |
| E→B | (k\equiv1) | 7 | (5k+7) |
| B→E | (k\equiv0) | 6 | (5k+6) |
| B→B | (k\equiv2) | 8 | (5k+8) |
| P2→E | (k\equiv1) | 1 | (5k+1) |

The residue condition in each row is exactly what makes (L(k)) divisible by three. Therefore, along a consecutive run of one edge type, the corresponding (3)-adic valuation drops by one per call. This explains the valuation parameters used by the E-chain residue cylinders and the P2K4/P2K7 special cases.

**Caveat:** the active linear form changes when the macro branch changes. Its valuation can therefore reset at a branch switch. The table is not, by itself, a globally decreasing rank function.

## 3. Finite residue-cylinder theorem

Fix a word of (n) continuing edge types, hence constants (c_0,ldots,c_{n-1}) from ({1,5,6,7,8}). If
[
3k_{i+1}=8k_i+c_i
]
at every step, then induction gives
[
3^n k_n
=8^n k_0+sum_{i=0}^{n-1} c_i,8^{n-1-i}3^i.
]
Since (8^n) is invertible modulo (3^n), this fixes **one and only one residue class for (k_0\pmod{3^n})** for that transition word.

Thus a proposed length-(n) E/B/P2 path is an exact (3)-adic cylinder, not a heuristic pattern. For a concrete root-reachable index, its first (n) macro branches can be decided from (k_0\bmod3^n), provided the packet resource and marker hypotheses are also satisfied.

## 4. What this does and does not settle

Existing source modules already establish substantial cylinders:

- `EChainAExit.lean`: arbitrary-depth E chains ending in A, with an explicit resource guard.
- `EChainBExit.lean` and `EChainDoubleBExit.lean`: selected B and B→B terminal cylinders.
- `P2K2Source.lean`, `P2K1Mod9Source.lean`, `P2K4Source.lean`, and `P2K7Source.lean`: verified fixed-tail P2-reset subfamilies.

The remaining work is to compose these cylinders along the *actual marker-mutating orbit*, especially when a P2 reset is followed by a marker family for which another P2 source transition has not yet been established. The resource condition for an E chain must also be checked at each reset. No all-(k) termination theorem is asserted here.

A productive next step is to take the exact root-reachable P2 index from the current blank-root chain, compute its residue-cylinder word only as far as needed, and discharge the corresponding source macro composition. Avoid promoting the branch-specific valuation identities to a global termination claim.

## 5. Lean check

The five affine identities and the three resource equations are formalized in [`IndexCocycle.lean`](IndexCocycle.lean). The file compiles locally with Lean 4.36.0-rc2. Its `#print axioms` output for all eight theorems is exactly `[propext, Quot.sound]`; there are no project-specific axioms, `sorryAx`, or classical-choice dependencies. This check validates the arithmetic identities only, not the source macro premises or the global orbit-termination question.
