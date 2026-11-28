# A direct infinite unary-sweep proof for a previously hard F412 cylinder

**Research status:** hand-checked mathematical induction with primitive simulation witnesses, not yet kernel-checked in Lean. The argument covers **every completion** of the sole missing `E1` transition. It is not conditional on the enormous F412 champion clock.

## Partial machine

Use states A–F, symbols 0/1, blank-0 tape, standard write/move/state notation:

| State | On 0 | On 1 |
|---|---|---|
| A | 1RB | **0LE** |
| B | 1LC | **1LD** |
| C | 1RF | 0LD |
| D | 0RE | 1LB |
| E | 1RC | **?** |
| F | **0LD** | 0RA |

Bold entries are the three alternative rows added to F412's eight fixed-row prefix. This is exactly the ordinary F412 depth6 A1=0LE, first-hole F0=0LD (index 3), second-hole B1=1LD (index 15) cylinder, with only E1 unassigned.

## Infinite family of exact configurations

Index tape cells by integers with the initial head at 0. For each `m >= 0`, let `C_m` be the configuration
- state **E**, head at `x=-2m-1`, reading a **0**;
- **1** at the single cell `x-1=-2m-2`;
- **0** at `x` and `x+1`;
- **1** at each of `x+2,...,0`, exactly `2m` cells (empty if m=0);
- all other tape cells **0**.

Thus the finite nonblank/active word, under the head marker, is `1 [E0] 0 (11)^m`, and all cells outside this finite word are 0.

**Theorem.** After exactly

```
T_m = 3m² + 7m + 11
```

primitive transitions from the blank tape, the partial machine is in `C_m`; every transition before that time is defined. Consequently, every total halting or ordinary completion of its missing E1 row runs forever without halting, because `T_m → ∞` and the entire shared run avoids E1.

### Base: T₀=11

Directly execute the eleven fixed instructions from the all-zero tape:

| Step | State | Head | Nonzero cells |
|---:|:---:|---:|:---|
| 0 | A | 0 | none |
| 1 | B | 1 | 0 |
| 2 | C | 0 | 0,1 |
| 3 | D | -1 | 1 |
| 4 | E | 0 | 1 |
| 5 | C | 1 | 0,1 |
| 6 | D | 0 | 0 |
| 7 | B | -1 | 0 |
| 8 | C | -2 | -1,0 |
| 9 | F | -1 | -2,-1,0 |
| 10 | A | 0 | -2,0 |
| **11** | **E** | **-1** | **-2** |

No transition reads E1. The last row is precisely `C₀`.

### Sweep lemma: a local 4-transition equality

Whenever an E-head marks the first of two adjacent zeros and the next two cells are ones, the four transitions

```
E0:1RC, C0:1RF, F1:0RA, A1:0LE
```

transform the local string

```
[E0] 0 1 1    → (4 steps) →    1 1 [E0] 0
```

leaving all other tape cells unchanged. The intermediate states C, F, A are on symbols 0,1,1 respectively; none sees the missing E1 row.

Starting from `C_m`, apply this lemma **m times**. It takes `4m` transitions and reaches state E at head `-1`, with contiguous ones in cells `-2m-2,...,-2` (length `2m+1`) and zero cells at `-1,0`, zero elsewhere. This is the *right-end configuration* `R_m`.

### Return/expansion lemma: exactly 2m+10 transitions

For any `m>=0`, from `R_m` perform:

1. `E0:1RC, C0:1RF, F0:0LD` — **3** steps, writing ones into cells `-1,0` and positioning state D on the rightmost one at `0`.
2. Repeat the alternating left-going instructions `D1:1LB`, `B1:1LD` for exactly **2m+3** steps. They traverse the newly enlarged contiguous run of `2m+3` ones in cells `-2m-2,...,0`; because its length is odd, they end in state B on the blank cell `-2m-3`.
3. Execute `B0:1LC, C0:1RF, F1:0RA, A1:0LE` — **4** steps. The resulting head is state E on `-2m-3`, with a one at `-2m-4`, zeros at `-2m-3,-2m-2`, ones on `-2m-1,...,0`, and zeros elsewhere.

The resulting tape is exactly `C_{m+1}`. Every E instruction during this return phase is E0; all other reads are the explicitly assigned rows above. Total transition count is `3+(2m+3)+4 = 2m+10`.

### Induction and nonhalting

Combining sweep and return:

```
C_m  --(4m steps)--> R_m --(2m+10 steps)--> C_{m+1}.
```

Every intermediate transition is defined; the combined length is `6m+10`. As

```
T_{m+1} - T_m = 6m+10,
```

the base row and induction establish every `C_m` at the claimed exact primitive time. In particular, for any finite number of steps `N`, choose `m` such that `T_m>N`; the partial machine has a defined run of at least `N` steps, hence **no completion of E1 can halt**.

**Validation:** An independent sparse-tape interpreter checked the complete configuration equality (including all nonzero tape cells and absolute head position) for every `m=0,...,40`, as well as the local transition identities above. The mathematical argument is inductive and does not rely on the 40-case check. To make the result kernel-certified, formalize the two local macro equalities against `Agent50Zipper` or the primitive `run` semantics and induct on m, reusing the existing completion/simulation lemma. A finite-window NGram closure failed for this cylinder through width 20; the parameterized sweep is materially stronger than that abstraction.
