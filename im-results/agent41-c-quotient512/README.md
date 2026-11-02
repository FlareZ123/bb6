# Agent 41: Machine C finite-quotient refinement to modulus 512

**Status (2026-11-02): intermediate, not a BB(6) solution.** This extends Agent 20's independently source-mapped quotient approach to modulus 128, 256 and 512; it does **not** classify Machine C. Sources: [Agent 20's mod-64 work](../agent20-c-quotient/README.md), [Agent 11's accelerated stopping criterion](../agent11-c-line/README.md), and [Agent 21's raw-machine semantic bridge](../agent21-c-source-bridge/CSourceBridge.lean). All novel numerical exclusions below are computational results with a Lean-checked transition soundness theorem; the finite 512-state-per-coordinate closure is separately cross-checked in JavaScript and C++, not Lean-kernel certified.

## Finite abstraction

Machine C is `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`, with exact blank-entry counter configuration `(5,0,1)`. For `M=8·2^r` (`r=3,4,5,6` here), let

`q_M(x) = x` when `x<8`, and `q_M(x)=8+((x-8)%M)` otherwise.

The abstract state space is `{0,...,M+7}³`. Each coordinate with abstract value below eight has one representative, itself; each coordinate with value at least eight has two representatives `u,u+M`. Draw an edge for every combination of the three coordinates' representatives whose exact `nextC` successor is defined, quotienting the successor coordinatewise.

Every real transition has an abstract edge, so absence of an abstract target from the blank-entry closure proves absence of any corresponding concrete target from the entire finite-time blank orbit. The nontrivial assertion has an explicit 512-modulus Lean proof in `Quotient512.lean.xz.b64`:

`Agent41.real_step_is_abstract_edge`, and the source-bridged `Agent41.published_step_is_abstract_edge` in `CMapBridge.lean`.

The proof uses `rep x = x` for `x<520`, and `rep x=520+(x-8)%512` for `x≥520`. Hence `rep x` is always one of the permitted representatives of `q x`. The case analysis proves the exact option-valued counter transition agrees after applying `q` to successor coordinates. `CMapBridge.lean` additionally proves pointwise equality to the **unmodified** `BB6CLine.nextC` from Agent 11, the same map already bridged to the original six-state machine by Agent 21. Successful complete unmodified-source [GitHub Actions CI run 41398359967](https://github.com/FlareZ123/bb6/actions/runs/41398359967), SHA `15b26018e9fd86a97863d5fb9ef5afc0e8c7c239`; its Lean 4.36.0-rc2 axiom audit for all three named theorems: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

## Exhaustive numerical census

| M | Abstract vertices | Reachable vertices | Representative edges | Excluded reset residues | Excluded side residues |
|---:|---:|---:|---:|---:|---:|
| 64 | 373,248 | 172,714 | 1,182,347 | 36 | 20 |
| 128 | 2,515,456 | 1,086,539 | 8,009,746 | 75 | 52 |
| 256 | 18,399,744 | 7,396,891 | 56,744,218 | 157 | 112 |
| 512 | 140,608,000 | 52,736,417 | 413,022,600 | 327 | 236 |

The 64 row reproduces Agent 20's previous certificate **exactly**. Both independent implementations agree on all 512 membership bits for reset and side families and on the aggregate 512 closure/edge counts. The BFS begins from `q(5,0,1)`, processes every reachable vertex once, and emits every representative transition. The reached set is therefore forward-closed by construction.

The reset family is `(2j+1,3j+4,0)` with `j≥4`. The side family is `(0,4n,24n+23)` with `n≥2`. For these ranges the quotient of each family depends only on its index modulo `M`, making the finite residue census valid for **infinitely many** natural indices once the transition-soundness and closure arguments are accepted.

## Residue classes newly excluded at each refinement

These lists contain exactly the exclusions at the refined modulus whose images were *not* already excluded at the previous modulus. Prior excluded classes lift automatically.

| Refinement | Additional reset indices | Additional side indices |
|---|---|---|
| 64 → 128 | `6,18,72` (mod 128) | `3,14,26,35,46,58,67,78,90,99,110,122` (mod 128) |
| 128 → 256 | `31,94,119,152,160,171,234` (mod 256) | `6,28,70,92,134,156,198,220` (mod 256) |
| 256 → 512 | `11,192,202,210,266,283,358,366,384,407,430,459,471` (mod 512) | `30,68,116,158,196,244,286,324,372,414,452,500` (mod 512) |

At modulus 512 the abstract filter excludes 327/512 reset residues and 236/512 side residues. These are **filters on necessary halting gateways**, not a nonhalting proof. Many candidate gateways still survive; a finer finite quotient by itself need not close them.

## Reproduction

- `quotient.cjs` uses Node.js standard library only; arguments `64`, `128`, `256`, `512` run the four censuses, each printing full excluded residue arrays. Source SHA-256: `37b1ada727cb66974e2b90b12e428ec26229ec229d7289a1969224f3a6c1d8e2`.
- `validate.cpp` independently implements the partial map, representative enumeration and graph closure, and prints every residue. Its modulus-512 counts and all residue flags match `quotient.cjs` byte-for-byte after output normalization. SHA-256: `fa84728fd78a49a24b238b21f8f7b4cb0eda98342064908f2b4cc05187efa4a2`.
- `Quotient512.lean.xz.b64` contains xz-compressed, base64-encoded UTF-8 Lean source. Decompress with Python's standard `base64` and `lzma` modules and verify SHA-256 **`58d27cdf96c62d7eeac74bf9dfe3b51c7a3f193b196c2b5b9f858ce657643b94`**. Compile under Lean 4.36.0-rc2. The source imports only `Std`.
- `CMapBridge.lean` imports the unmodified Agent 11 `CLine.lean` and the reconstructed `Quotient512.lean`. Manual, commit-trigger-free workflow: [`.github/workflows/agent41-c512-verify.yml`](../../.github/workflows/agent41-c512-verify.yml).

## Boundaries and next questions

A source-checked local proof of abstract-edge soundness does not itself certify the 52-million-vertex closure inside Lean. Upgrading the closure to a small independently checked finite certificate or a Lean-executable decision proof remains a valuable further step. More consequentially, this finite abstraction leaves nonexcluded residue classes even at modulus 512. Researchers should seek a **uniform global invariant** or a better forward section reduction that can decide the surviving infinite families. The numeric refinements are preserved here under `im-results/` rather than the publishable `results/` directory.
