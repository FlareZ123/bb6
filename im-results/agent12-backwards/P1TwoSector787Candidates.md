# P1 n≡18,34 (mod64): 787 exploratory affine inverse-cone candidates

Agent 12, 2026-11-02. **Intermediate, UNPROVED aggregate; not an academic result.**

Following the fully original-source verified 187-family n≡14(mod16) aggregate, I scanned even critical exponents in the previously unresolved n≡18 or34(mod64) sectors. The exact affine coefficient checker found **787 distinct candidate R modulo65536** whose finite inverse cones appear to terminate entirely in the previously source-established modular/power obstructions.

The complete reproducible **candidate list and attempted aggregate kernel proof** are preserved as `im-results/agent12-backwards/P1RAffineTwoSector.lean.xz.b64`, decompressed SHA-256 `e8e76bc36bbe42253c68f55adc87185df407c7669e15b31586df5d222cf2a422`. It imports `P1RAffineGeneral.lean` and proposes `blank_no_critical_two_sector`, which would certify every `n=65536*q+R` for the listed 787 R. All list entries satisfy R%64=18 or34, separating them from the existing Agent1 source-certified entire n%64=2 or50 sectors and other n≡14(mod16) results.

**Important validation boundary:** The first manual [source CI 41530659720](https://github.com/FlareZ123/bb6/actions/runs/41530659720) spent substantial time computing the 787-family aggregate. Until a successful source-level run completes, **do not treat all 787 as proved**. Experimental Python traversal and local mock Lean typechecking are not substitutes for the original source/axiom audit.

To avoid a costly indivisible proof, subdivide the existing candidate `twoSectorResidues` into ~10-40 lists and individually kernel-certify `chunk.all twoSectorOK=true`, then combine with `List.all_append`. Potentially separate the chunks into multiple CI jobs; the current aggregate `by decide +kernel` may be spending too much time on a long list. A local sharding prototype is straightforward; the mathematical soundness is already separately source-proved in `goodAff_sound_general`.

A first independent source candidate sublist `[226,418,466,482,546,674,802,914]` is at `im-results/agent12-backwards/P1RAffineTwoSectorSeeds.lean`. Their source CI check is separate from the unverified 787-family aggregate. Once accepted, these eight genuinely new infinite index families can be promoted to `results/`, while the full 787 list should remain intermediate until audit completes.

Any certificate here is a **necessary critical-gateway exclusion only**, and does not establish P1 or BB(6) nonhalting.
