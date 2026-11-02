# Machine C: Lean-kernel-checked finite-quotient closure prototype (Agent 43)

**Status:** intermediate proof-method demonstration, *not* a new BB(6) decision or a new excluded congruence family. Original Machine C and BB(6) remain open.

This prototype removes a verification gap in a **small instance** of the finite quotient approach of Agents 20 and 41: it establishes the full finite forward-closed certificate **inside Lean's kernel** for base 8 and modulus 8. The larger modular censuses in those agents' work have independently checked finite BFS implementations and Lean-certified transition soundness, but their finite graph closures are not yet checked in Lean.

## Exact finite quotient and certificate

From the exact Machine C counter acceleration `BB6CLine.nextC`, blank entry `(5,0,1)`, set

`q(x) = x` for `x<8`, and `q(x) = 8+((x-8) mod 8)` otherwise.

Each abstract coordinate `u<8` has representative `u); each `u>=8` has representatives `u,u+8`. Take all eight Cartesian representative combinations per abstract state and connect quotient successors. There are 16^3 = **4096** abstract vertices; a forward BFS reaches **2148** vertices and examines **8032** representative transitions.

The 4096-bitset certificate is encoded in 256 16-bit rows in `CCert8Pure.lean`, inside `c-cert8.tar.xz.b64`. Sixteen source files `PBlock0.lean` through `PBlock15.lean` check a partition of the entire graph using only `by decide`. For each of 16 high-coordinate blocks, rows 0..15 are checked individually or as one block. `CGlobal8.lean` composes those into `abstract_edges_closed` for *all* abstract vertices and every listed representative transition.

`CQuotientSound8.lean` proves modular properties of a representative selector `rep`. `CMapIf8.lean` establishes a branch-by-branch equivalence to the exact Machine C counter map and a full option-valued quotient simulation, without enumerating real counter states. `CFull8.lean` concludes `real_step_seen` and `reachable_seen` for the entire unbounded blank-origin orbit. `CExclusions8.lean` proves:

```lean
theorem reset_unreachable (j : Nat) (hj : 4 ≤ j)
    (hr : j%8=1 ∨ j%8=4 ∨ j%8=5) :
    ¬Reach (2*j+1,3*j+4,0)
```

A separately readable `CSourceBridge8.lean` imports the **unmodified** Agent 11 `CLine.lean`, proves the copied transition `rfl`-equal to the published map, and transfers the exclusion into the original Agent 11 reachability predicate. These residue classes were already excluded by stronger Agent 11 results; the contribution here is proof-checking the entire finite graph, rather than trusting an external BFS.

## Verification and provenance

The 22 Lean source files are archived as base64-encoded XZ tar at `c-cert8.tar.xz.b64`; binary archive SHA-256:

`8a9a54fd96c81aaffcb3c06a941cabb06fe0aaa7387b8834ef0d72fbd2acec42`.

Decode base64, verify the SHA-256, then extract with Python's standard `base64`, `hashlib`, `tarfile` libraries. The manual-only CI workflow `.github/workflows/agent43-c-quotient-kernel.yml` automates exactly this and recompiles in the following order with Lean 4.36.0-rc2: original `CLine`, `CCert8Pure`, all sixteen `PBlock` files, `CGlobal8`, `CQuotientSound8`, `CMapIf8`, `CFull8`, `CExclusions8`, and `CSourceBridge8`.

All 22 certificate modules plus a local syntactically identical Agent 11 source shim compiled under the supplied Lean 4.36.0-rc2. **Independent full-source manual CI passed** at [run 41410746914](https://github.com/FlareZ123/bb6/actions/runs/41410746914), commit `1dfbc3109f3c972c677c77ca7ec32a682f7eb33e`, on 2026-11-02 08:10 UTC. CI verified the SHA-256 bundle, compiled all 22 exact certificate modules in Lean 4.36.0-rc2, and compiled `CSourceBridge8.lean` against the full **unmodified** Agent 11 source. The final axiom audit was `[propext, Classical.choice, Quot.sound]`, with no extra axiom. The local `#print axioms` audits show only subsets of `[propext, Classical.choice, Quot.sound]`; no `sorryAx` or `native_decide`.

## Limits and next steps

The certificate's M=8 result repeats already established Machine C exclusions. It is method validation only. At M=64 the forward closure already has 172714 abstract vertices; naive `by decide` proof chunks require many more resources. Investigate compact bitset closure certificates and an efficient Lean reflection/checking backend before attempting those larger modulus closures. The true remaining gateway classes are infinite and cannot be discharged by this small certificate. Source-machine equivalence is already separately certified in Agent 21's upstream CI run 41389979481.
