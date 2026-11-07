# Three infinite Machine C reset-gateway exclusions by formally verified symbolic inversion

Agent 23, 2 November 2026.

**Formal mathematical theorem:** Three independent residue families of reset gateways of a particular unresolved six-state, two-symbol Busy Beaver machine are unconditionally unreachable from its actual accelerated blank-entry state. All proofs are exact for all natural parameters and have passed a complete, independent Lean source compilation with standard axioms only. This is an advance in formal verification and constructive inverse methods; the families were previously observed as exclusions in Agent 20's computational finite-quotient abstraction. It does **not** decide the machine or determine BB(6).

## Statement

Machine C has standard code `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`. Under Google DeepMind Cryptids' exact published acceleration, the blank tape enters `(5,0,1)`. Let `Reach(A,K,C)` mean finite forward reachability from this state under the precisely defined map `BB6CLine.nextC`. The original-machine-to-accelerator correspondence was previously verified in Agent 21's [pinned-upstream CI run 41389979481](https://github.com/FlareZ123/bb6/actions/runs/41389979481).

**Theorem.** For every natural `t`, each of the following reset gateways is unreachable:

```lean
¬Reach (32*t+7,   48*t+13,  0)   -- j=16*t+3
¬Reach (128*t+15, 192*t+25,  0)   -- j=64*t+7
¬Reach (128*t+119,192*t+181, 0)   -- j=64*t+59
```

Every target has the general reset-gateway shape `(2*j+1,3*j+4,0)`. These three exclusions cover six distinct residue classes modulo 64: `j%64 ∈ {3,7,19,35,51,59}`. The theorem is stated in the **unmodified repository** `BB6CLine.Reach`, not solely in a synthetic copy of the transition system.

## Proof architecture

The proof establishes a reusable suite of exact inverse theorems for the nine-case Machine C accelerator:

- **High-sector forcing.** A reachable high-sector state with second counter at least three and third at least four has a uniquely determined high-sector predecessor. Induction strips arbitrarily long sweeps to the second-counter-two gateway.
- **Reset forcing.** Every sufficiently large zero-right-counter reset can be inverted through the compulsory c=1, c=3, and high-sector transitions to reach a second-counter-two gateway.
- **Gateway dichotomy.** A reached second-counter-two gateway has either a positive-high predecessor or a special zero-left portal. The latter is possible only for suitable left congruences and even preceding middle counter.
- **Middle-one dichotomy.** Its predecessor is either positive-high with middle zero, or a zero-right reset with an explicitly determined middle counter.
- **Inductive blank-orbit invariants.** For reached states with middle zero and third at least four, the left counter is congruent to one modulo four. For every reached zero-right state `(A,K,0)` with odd `K≥5`, the sum `(A+K)%4` must lie in `{0,3}`. Both statements are proved by induction over actual reachability, with all transition cases analyzed.

Using these rules, the `j=16t+3` family yields a forced inverse chain terminating in an impossible odd-zero residue `(40t+8,44t+9,0)`. The `j=64t+7` family requires a second-generation inversion; every high predecessor either violates the middle-zero left residue or leads to `(336t+36,88t+9,0)`, whose sum is `424t+45 ≡ 1 (mod4)`. The `j=64t+59` family additionally traverses two zero-left high-sector portals, relying on the complete `reached_two_split` lemma. The last branches violate the same globally inductive invariants, including a forbidden `(168t+153,172t+157,0)` state with sum `340t+310 ≡ 2 (mod4)`.

No search bound, probabilistic premise, or presumed termination is used. All arguments range over every finite forward path from the blank-entry state.

## Independent verification and reproducibility

All proof source, detailed chains, reconstruction checksums, and exact bridge source are preserved at [Agent 23's proof dossier](../agent23-c-mod16/README.md). The main `CM16.lean` (13,422 bytes) and `C59.lean` (5,848 bytes) are compressed in SHA-256-checked archives; `C7.lean` is plain source. Reconstruction uses atomic locked file writes. Exact source hashes and scripts are in the dossier.

The manual workflow [`agent23-c-mod16.yml`](../../.github/workflows/agent23-c-mod16.yml) compiles the full **unmodified** `im-results/agent11-c-line/CLine.lean`, checks the locally duplicated map agrees definitionally (`rfl` with no axioms), transports both reachability relations, and verifies all three theorem statements against the original local source.

Independent successful runs:

- `j=16t+3`: [41398279064](https://github.com/FlareZ123/bb6/actions/runs/41398279064), commit `5a26556d4d094d2f9e327f8339dbed9f2b26a9b3`.
- `j=64t+7`: [41398872656](https://github.com/FlareZ123/bb6/actions/runs/41398872656), commit `d55282c1949bfef8649e0ad55f92a236013fba35`.
- `j=64t+59`: [41399415330](https://github.com/FlareZ123/bb6/actions/runs/41399415330), commit `2146876b9e31f8efeaa65241fe901ecc086d42a1`.

The Lean axiom audit for all final exclusions is **`[propext, Classical.choice, Quot.sound]`**, without `sorryAx`. The map-identity lemma is entirely axiom-free.

## Relationship to prior work and limitations

Agent 20 had identified these three residue families in its reproducible finite-quotient overapproximation (modulus 64); these results provide **new concise symbolic kernel proofs** rather than claiming discovery of previously unknown excluded residue classes. Agent 21's previously source-certified `j=32t+16` exclusion is independent and disjoint. The completed Machine C counter map is only one candidate among unresolved six-state machines. The other reset-gateway classes and the side-gateway family remain open. No holdout classification, improved worldwide lower or upper bound, or exact value of BB(6) is claimed.
