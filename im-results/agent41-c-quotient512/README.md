# Agent 41: Machine C finite-quotient refinements through modulus 1024

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

## Independently checked extension to M=1024 (06:26 UTC)

The same exact quotient construction was computed at modulus **1024**, yielding **1,099,104,768** possible abstract vertices, **385,473,152** reachable vertices, and **3,050,991,229** examined representative edges. The set excludes **678/1024** reset-gateway residues and **540/1024** side-gateway residues. All numbers and **every one of the 2048 individual gateway flags** agree exactly between two independently implemented C++ graph traversals: an original byte-array BFS with lazily allocated queue and a new compact bitset traversal (`validate_bits.cpp`). The second implementation uses approximately 1.64 GB peak RSS and completed in approximately 89.5 seconds on the local environment. Its source SHA-256 is `bcc6d010d0c75a3e2acfee087284c6423d6cb0ab1f963ebc51efac85657e55db`.

**Precisely new exclusions beyond lifting the M=512 residue sets**, for all indicated natural indices:

- Reset `j>=4`, `j%1024` in `{8,74,96,154,256,271,311,338,343,376,395,424,454,550,610,696,738,750,798,875,879,927,938,1016}`.
- Side `n>=2`, `n%1024` in `{12,24,38,42,50,55,84,120,136,146,147,155,162,179,190,191,202,268,280,294,298,306,311,340,376,392,402,403,411,418,435,446,447,458,524,536,550,554,562,567,596,632,648,658,659,667,674,691,702,703,714,780,792,806,810,818,823,852,888,904,914,915,923,930,947,958,959,970}`.

The 1024-modulus **unbounded transition soundness** is independently checked in Lean 4.36.0-rc2, in `Quotient1024.lean.xz.b64` (decompressed SHA-256 `428771b347719b0c1f9f54d01fc69f3d78abed3dc5e8dd5882c806fc9fc29585`) and `CMapBridge1024.lean` (source SHA-256 `c6af3d86da25ac43b679434fbd1c806a0740038c91d891d1119583d5090c3227`). The full, unmodified Agent 11 `CLine.lean` source and these proofs compiled successfully in [manual pinned-source CI run 41399745807](https://github.com/FlareZ123/bb6/actions/runs/41399745807); final axiom audit reports `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. See [manual workflow](../../.github/workflows/agent41-c1024-verify.yml). The finite BFS itself remains double-checked externally rather than Lean-kernel certified.

**Important:** This additional refinement still leaves 346 reset residues and 484 side residues at modulus 1024 not excluded by this quotient. The goal of deciding the complete Machine C blank orbit, and hence BB(6), remains open. No universal upper bound or halting decision is claimed here.

## New source-certified M8 all-time section exclusion (2026-11-02)

The separately documented [M8 forbidden cylinder and stopping-parameter sieve](./NEW-M8-HALTING.md) uses Agent43's **complete Lean-kernel-checked** M8 quotient closure, which is stronger as a verification artifact than this directory's M512/M1024 computations. From the exact original CLine blank-entry acceleration, it proves `¬BB6CLine.Reach (8*u+7,8*v+4,0)` for all naturals `u,v`, and excludes **two infinite two-parameter classes** `(j%8,m%8)=(2,7)` or `(6,3)` from Agent15's exact odd-first-counter halting equation. All-time original-source CI [41473492769](https://github.com/FlareZ123/bb6/actions/runs/41473492769) passed with standard axioms only, no sorry. This is a proper mathematically meaningful new section restriction, but **does not decide Machine C or BB(6)**. The two independent reusable finite quotient engines [C++](./parametric-quotient.cpp) and [Node.js](./parametric-verify.cjs) are also preserved here; variable-base experimental reset/side improvements were already proved by other agents, so we do not misrepresent those as frontier advances.
