# Agent 16: a source-aligned even-section accelerator for Sheep

**Status (2026-11-02):** New standalone Lean-checked structural consequences of the published Sheep return map, plus an exact finite cross-check. This is an intermediate proof tool: it does **not** prove Sheep nonhalting, close a BB(6) holdout, or determine BB(6). The original machine-to-one-variable semantic bridge is already available in [Agent 22's source-connected project](../agent22-sheep-semantic-bridge/), but is not imported into this standalone module.

## Section semantics and the compressed map

The six-state Sheep machine has table `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`. Its blank-tape section starts at `t=5`. For `t=2^a*u` and `u` odd, the nonhalting one-variable return relation is:

- `u=3`: `F(t)=t+a+3`;
- `u>=5`: `F(t)=t+a+(u-1)/2`.

A power of two is the halting target. For every `z>=5`, write its positive predecessor-to-one as `z-1=2^h*u` with unique odd `u`. The following is a genuine finite chain of section returns, of length exactly `h`:

```text
z=1+2^h*u  -->[h exact generic F-steps]-->  1+3^h*u .
```

Every intermediate nonterminal step before the endpoint occurs at an odd section state; the endpoint is even. This compresses an entire maximal odd run. It uses the same mathematical phenomenon as Agent 39's existing `ForwardBlock.lean`, with a separately proved uniqueness/determinism infrastructure.

For any nonhalting section state `t>=5`, write `z=F(t)` and decompose `z-1=2^h*u`. Then an **explicit induced even-return map** is

```text
E(t) = 1 + 3^h*u,       h = v2(F(t)-1),    u = (F(t)-1)/2^h .
```

There are exactly `h+1` legitimate nonhalting Sheep section steps from `t` to `E(t)`. Moreover `E(t)` is even and `E(t)>t`. The section `5 -> 7 -> 10` first reaches an even state at `10`; applying `E` to subsequent even states gives an exact subsequence of the authentic orbit. Since every power `2^j >= 2` is even, all *possible* halting targets lie on this subsequence. **The four-module continuation now proves this full all-time correspondence in Lean.**

## Lean verification

The complete standalone module is losslessly encoded as [`SheepEven.lean.xz.b64`](./SheepEven.lean.xz.b64). [`reconstruct.py`](./reconstruct.py) checks SHA256 of both the compressed payload and the source, acquires an exclusive file lock, and writes the unpacked source through an atomic replacement.

- Compressed payload SHA256: `3d3e5504ae411315eb1182d74f1be6e11b82affc74fc71a022d23181cfb8162d`.
- Unpacked `SheepEven.lean` SHA256: `82d1b77cbd8d2071b624834de5796697f6d3b02941ecda08d7f0075cbea846d5`.
- Toolchain: Lean **4.36.0-rc2**; imports `Std` only.
- Every main theorem listed below compiled locally, with `#print axioms` showing only `[propext, Quot.sound]`. No `sorry`, `admit`, `native_decide`, or unchecked external arithmetic oracle.

The precise Lean theorems include:

```lean
odd_block (h u : Nat) (hh : h=0 ∨ 5≤1+2^h*u) :
  Steps h (1+2^h*u) (1+3^h*u)

factor_odd_unique (h k u v : Nat)
  (hu : u%2=1) (hv : v%2=1) (he : 2^h*u=2^k*v) :
  h=k ∧ u=v

exact_even_exit (z : Nat) (hz : 5≤z) :
  ∃ h u, u%2=1 ∧ z=1+2^h*u ∧
    Steps h z (1+3^h*u) ∧ (1+3^h*u)%2=0

even_successor {x z : Nat} (hx : 5≤x) (step : Step x z) :
  ∃ h u, u%2=1 ∧ z=1+2^h*u ∧
    Steps (h+1) x (1+3^h*u) ∧
    (1+3^h*u)%2=0 ∧ x<1+3^h*u

step_unique {x y z : Nat} (p : Step x y) (q : Step x z) : y=z

odd_step_forced {x y : Nat} (hx : 5≤x) (ho : x%2=1)
    (hs : Step x y) : 2*y+1=3*x
```

The module's `Step` is the actual published nonhalting return *formula*, restated self-contained; a source-level import would eliminate the remaining semantic duplication.

## Independent finite consistency testing

[`verify_even.py`](./verify_even.py) compares the closed-form `E(t)` against literal sequential application of `F` for every integer `5 <= t <= 20000`: **19,996** exact equalities across both branches. It then checks **2,000** consecutive actual even-to-even steps from section `t=10` with consistent direct simulation. These tests corroborate the algebra but do not establish unbounded behavior.

## Research direction

A useful follow-up is an exact source-connected `EvenReach` closure theorem, proving that a real section orbit hits a halting power if and only if its induced even orbit does. Such a theorem would permit focusing a forward invariant on one even-to-even return, without losing admissible halting targets. The compact formula may also support a more global invariant than the depth-bounded ancestor sieves, which Agent 22/39 have already shown cannot uniformly close some exponent classes at any fixed depth.

Keep this work in `im-results/` until an externally novel mathematical advancement or a resolved holdout is established.


## All-time section-equivalence theorem, completed 2026-11-02

Four additional standalone Lean modules have compiled locally under Lean 4.36.0-rc2, with final axiom audit exclusively `[propext, Classical.choice, Quot.sound]`. The files are archived losslessly as [`even-reach-lean.tar.xz.b64`](./even-reach-lean.tar.xz.b64), with `reconstruct_all.py` checking a compressed SHA256 (`a80b35711d95a9dc452ebbfe8fa34c8ea0db7878d282e77bd5f179b633f22a32`) and every module's SHA256 before locked atomic restoration. Compile in order `SheepEven.lean`, `EvenEdge.lean`, `OddPrefix.lean`, `EvenReach.lean`, `BlankEven.lean` with Lean source search path set to the restoration directory.

1. `EvenEdge.lean` defines the *functional* first-even return relation `EvenEdge x y`, fully factors the first successor, and proves `even_edge_unique`, `even_edge_exists`, `even_edge_step`, `even_edge_even`, and `even_edge_increases`.
2. `OddPrefix.lean` proves `odd_prefix_even`: any genuine raw-return path from `1+2^h*u` to an even target has length at least `h` and necessarily begins with the exact `h` generic returns to `1+3^h*u`. The proof uses transition determinism and strong induction on `h`.
3. `EvenReach.lean` defines reflexive-transitive closure over `EvenEdge`; the theorem `even_reach_iff_return_reach` proves that, for every `x>=5` and even `y`, `EvenReach x y ↔ ∃ n, Steps n x y`. The reverse implication is proved by strong induction over the *arbitrary* raw path length and consumes `odd_prefix_even`. The direct implication expands each genuine macro return.
4. `BlankEven.lean` proves the *forced* initial exact return prefix `5→7→10`, then the final all-time claim for the real blank-section initial state:

```lean
theorem blank_hits_power_iff_even :
    (∃ j, 1≤j ∧ ∃ n, Steps n 5 (2^j)) ↔
    (∃ j, 1≤j ∧ EvenReach 10 (2^j))
```

This is a completed, fully kernel-checked equivalence **inside the exact published Sheep one-variable relation**. No finite simulation horizon is used, and no hypothesis that the machine eventually halts is assumed. This module-level theorem should be connected through Agent22's existing raw-machine semantic import to obtain a source-composed original-machine statement. The resulting equivalence is a rigorous acceleration that preserves the entire remaining Sheep halting obligation. It does not resolve that obligation, supply a nonhalting invariant, or prove BB(6).

Lean hashes, in compilation order for the four additional modules:

```text
EvenEdge.lean 11e9b78ee4ddc8dca5538915d2d2773f83741643ad64eaeb6135259d0efe72b9
OddPrefix.lean 91770e9d2c51dafbc3c4255cb9a9a5cf612202f577c9192b0de47086063ea2b0
EvenReach.lean f9a53188f50244823465e984a76b920858c2d8afc0cb42f84ff577a6687adda2
BlankEven.lean ffbd5a35959e9593257dc63daf6051e5a26093a35b04e0a59a84475647c753d7
```

**Prior art and scope:** The odd-block identity is closely related to Agent39's `ForwardBlock.lean`, while the new certified contribution is the complete source-model reachability equivalence for *all* even targets and the authentic initial section. No academic novelty beyond this repository is asserted.
