# Agent 10: exact nonmerging of two rooted S-section counter orbits

**Scope:** a source-checked number-theoretic property of the published S high-level map, with a genuine two-root application. **Intermediate**: the actual six-state Turing machines remain unclassified, and no BB(6) upper or lower bound is improved.

- Source: [`QOrbitDisjoint.lean`](./QOrbitDisjoint.lean), Lean **4.36.0-rc2**, compiled locally and in [manual source CI 41469546196](https://github.com/FlareZ123/bb6/actions/runs/41469546196).
- Only standard axioms in `#print axioms`: `[propext, Classical.choice, Quot.sound]` for the final theorem, and only `[propext, Quot.sound]` for the single-step injectivity theorem; no `sorryAx`.
- Mathematical source of the map: Google DeepMind's two [S-root](https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB.lean) and [T-root](https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/M_1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RBHHH.lean) high-level accelerators. Both root entries and their symbolic parameters were **already established in the upstream formalization**. This investigation claims no new blank-entry discovery.

## Source-compatible arithmetic map

Use the previously published S-section coordinate `q=b+16`. While the actual S section survives (before a potential transfer from `c=0`), its first counter follows the exact map

```text
F(q) = 4*(q/3)                   if q % 3 == 0
     = 4*floor(q/3) - 3          if q % 3 == 1
     = 4*floor(q/3) + 1          if q % 3 == 2
```

where divisions are natural-number floor divisions. The Lean theorem `qNext_bShift` directly proves `F(b+16)=bNext(b)+16` for the published three residue branches `bNext`, without assuming a direct import of the separate upstream Cryptids `Cfg` representation.

For every `q>=16`, `F(q)>q` and the image belongs to the **invariant residue set** `G={q>=16 : q mod 4 in {0,1}}`. More surprisingly, `F` is **injective on G**. This is the kernel-checked theorem `qNext_injective_good`, proved exhaustively by combined mod-3/mod-4 arithmetic and `omega`. Therefore equal later iterates in G uniquely determine equal earlier iterates at any matched step count.

## General all-time separation theorem

`qIter n q` denotes `F^n(q)`. The Lean theorem `qIter_disjoint_of_gap` proves, for **any** two seeds `a<b` in G and any index `k`, if

```text
F^k(a) < b < F^(k+1)(a)
```

then

```text
F^m(a) != F^n(b)   for every m,n >= 0.
```

This general statement combines strict growth, closed-class injection, exact iteration composition, and a finite gap witness. It is **unbounded in both iteration indices**, with no numerical simulation assumptions.

## Application to the existing two genuine blank entries

The independently documented original rooted T machine enters S with `b=1,c=3`, hence **q=17**; the original rooted S machine enters S with `b=125,c=3`, hence **q=141**. The finite prefix of the q=17 section trajectory is:

```text
17, 21, 28, 33, 44, 57, 76, 97, 125, 165, ...
```

Thus `F^8(17)=125 <141<165=F^9(17)`. Both seeds lie in G. By the general theorem,

```lean
rooted_q_orbits_disjoint (m n : Nat) :
    qIter m 17 ≠ qIter n 141
```

is established **for all** natural `m,n`, without assuming the roots' nonhalting status.

**Precise implication:** The two original rooted blank executions cannot occupy the same S-section first-coordinate value during their respective **initial uninterrupted S phases**, so a merger inside those S phases is ruled out even with arbitrary time offsets. The complete physical tapes might still meet by another route after a transfer to `T`, and such transfers remain unresolved. This result does **not** certify whole-machine non-merging, either halting outcome, or BB(6).

## Reproducibility and research priority

Run the standalone `QOrbitDisjoint.lean` under Lean 4.36.0-rc2 or use the manual-only [workflow](../../.github/workflows/agent10-s-orbit-separation.yml). The proof uses only core Lean/Omega and contains no external compressed dependency.

The injectivity mechanism is an elementary arithmetic observation and could have been noted elsewhere; priority over the existing Busy Beaver literature has **not** been established. For this reason the result is stored in `im-results/`, with no claim of an academically publishable classification. The main research value is an all-time certified exclusion of a tempting two-root shared-counter shortcut and a reusable invariant-class criterion. The next serious problem remains proving actual never-transfer/nonhalting for q17 or q141, or discovering a genuine halting route.
