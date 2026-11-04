# S4 reduced-map inverse collisions and halting fans

**Agent 5, 2026-11-04. Intermediate mathematical result.** These are universal arithmetic theorems about the exact *source-shaped compact S4 return transducer* established in `im-results/agent3-s4-weighted-drift/`. They do **not** prove raw S4 halting or nonhalting or determine BB(6). Original-source end-to-end transport of the compact map remains a separate verification obligation. Keep this dossier in `im-results/` pending novelty review and source-connected synthesis.

## Results and scope

Let `F = S4Collision.compactNext : List Nat → Option (List Nat)`, defined in [Collision.lean](Collision.lean), importing Agent 3's verified source-shaped `H`. This is the previously studied source-mirrored S4 32-epoch reduced return rewritten in compact one-list form. Its first digit after a successful step is increased by 17. The helper `H(a,L)` consumes odd head digits recursively, and on even head `a=2q≥2` returns `[q+2,b+q]++S` for `L=b::S`.

1. **Genuine-reduced-seed inverse ambiguity:** for all `u,v,t,S`, the distinct inputs
   `A=[80,150+2u,481+u+2v,t]++S` and
   `B=[80,145+2u,192+v,t+294+u+v]++S`
   have `F(A)=F(B)`. The modeled seed `[42,12,8,5]` reaches `A=[80,150,481,133,28,25]` after precisely 13 reduced iterations and `F(A)=F([80,145,192,427,28,25])=[79,106,296,427,28,25]`. `Collision.lean` proves both the parameterized equality and this rooted finite witness. The second parent is *synthetic*, with no actual-root reachability assertion.

2. **Unbounded one-step in-degree:** for every `n`, the state `[79]++replicate (n+2) 100` has at least `n+1` distinct immediate predecessors. Explicit parents: `[80,133,2]++replicate n 100`, and for `0≤k<n`,
   `[80,138]++replicate k 100++[95,2]++replicate (n-1-k) 100`. `UnboundedCore.lean` proves the odd-branch stationary loop `H 201 (100::S) = (H 201 S).map (100::·)`; `UnboundedDegree.lean` proves the distinct-predecessor theorem.

3. **Unbounded in-degree directly on terminal gates:** for each `n`, the halting state `Y_n=[80]++replicate (n+3) 62++[0]` has at least `n+1` pairwise distinct predecessors
   `P_{n,i}=[82,61]++replicate i 62++[57,2]++replicate (n-i) 62++[0]`, `0≤i≤n`. Exactly `F(Y_n)=none` and `F(P_{n,i})=some(Y_n)`. This is `S4Collision.unbounded_halting_indegree` in [HaltingFan.lean](HaltingFan.lean).

4. **Strictly positive terminal gates and parents:** changing each final digit `0` above to `64` preserves all predecessor equations and the terminal gate. Thus `Y'_n=[80]++replicate (n+3) 62++[64]` and all constructed parents have strictly positive digits, with `F(Y'_n)=none` and at least `n+1` distinct predecessors. This is `S4Collision.unbounded_positive_halting_indegree` in [PositiveFan.lean](PositiveFan.lean). The result excludes a zero-digit artifact.

The terminal witnesses are **synthetic**. Whether a terminal stack with any of these properties occurs on the actual seeded reduced orbit is entirely open. Infinite inverse branching does not establish any actual-root halting, and finite rooted collision does not imply two different histories are genuinely reachable.

## Reproduction

Compile with the supplied **Lean 4.36.0-rc2**:
`S4WeightedDrift.lean → S4SourceShape.lean → Collision.lean → UnboundedCore.lean → UnboundedDegree.lean → HaltingFan.lean → PositiveFan.lean → SourceTransfer.lean`.
Reconstruct the first two modules from Agent 3's lossless XZ+Base64 files at `im-results/agent3-s4-weighted-drift/`. Set `LEAN_PATH` to the directory of each previously compiled importable `.olean` and compile prerequisite modules in order. All five compiled locally with Lean 4.36.0-rc2 and each final printed theorem reported **only `[propext, Quot.sound]`**; no `sorry`, `admit`, `native_decide` or custom axioms.

Source-file SHA-256 (local UTF-8):
- `Collision.lean`: `fbab20262e0b3021aabd18c5d9016f03c6609b39879b19b040fbb42f970dd740`
- `UnboundedCore.lean`: `aff01b4e40c496ee3cc22677ebe95db674cffe5f7257f78db773d8a6f35d38c4`
- `UnboundedDegree.lean`: `edf1a960b35d142c4c3693e745d497ac24e2d121c988b9f9b6ea205e469050b8`
- `HaltingFan.lean`: `02e24311009bae1dcc6b5174861d3a50ced5c7d416b2d45b4cf0225c900545d5`
- `PositiveFan.lean`: `a8a52f1dcdff064f066f6225065c375dc62e72a9d3acbbad05d5ec2a8accec73`
- `SourceTransfer.lean`: `e7060b5e0c35273be53e434a295d9e892ab440bf3567753b706af7f67db12b32`

The partial map was already mathematically characterized and Lean-proved equivalent to a copied S4 source-shaped reduction by Agent 3 at [S4 weighted drift](../agent3-s4-weighted-drift/README.md). Agent5's [source bridge](../agent5-s4-source-bridge/README.md) was originally source-checked by CI, but *this particular compact transducer-to-genuine-source composite* has **not** yet passed a single direct unchanged-source compilation. Kernel verification of these five standalone modules establishes their internal mathematical statements only.

## Consequences and next work

This demonstrates that the inverse graph around S4 halting gates has no uniformly bounded one-step branching factor, even when restricted to strictly positive digits. It rules out any backwards search implementation that assumes a global finite fan-in constant. It does **not** rule out source-specific inverse algorithms with length-dependent bounds.

Useful follow-up: prove a source-connected compact-map equality and investigate *seed-sensitive* inverse restrictions. A uniform classification of synthetic predecessor families alone cannot decide S4. Compare external S4 inverse dynamics literature before describing any of this as academically novel.

## Source-shaped transport strengthening (2026-11-04)

[SourceTransfer.lean](SourceTransfer.lean) now imports the **unchanged, SHA-checked** Agent 3 `S4WeightedDrift` and `S4SourceShape` modules. The new `Collision.lean` directly reuses their `_root_.H` helper, proves its `bumpBy 17` agrees with their `bump17`, and proves `compactNext_eq_source` for **all** lists. The transport module proves `compact_source_equivalence`, the arbitrarily high **positive halting-target** in-degree for `S4SourceShape.sourceReduced`, and a seed-rooted inverse collision for `S4SourceShape.sourceRun 13 [42,12,8,5]`. The final printed Lean axioms are exactly `[propext, Quot.sound]` on local Lean 4.36.0-rc2. All proof files are in the repository and verified locally. This is a concrete source-shaped *definition-equivalence proof* beyond purely empirical correspondence. Import against **unchanged original Cryptids S4** is a different, still-open final source connection.

Agent 3 prior Lean source raw SHA-256: `S4WeightedDrift.lean` `ab696fc6c6c27b6518cb78ffd0e9dda5292d39dbcea5fee98ae6b75f4735bba2`, `S4SourceShape.lean` `befc80875686ccc7e15ab0c02e114e7bbed86821b5d7442e35bb0ae19ee24539`. They were reconstructed and locally compiled unchanged before the transport proof. The statement is not a fresh original-Cryptids-namespace CI certificate, and no claim that a synthetic halting stack occurs from the true blank seed follows.
