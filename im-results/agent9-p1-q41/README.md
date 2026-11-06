# Original-source P1 fixed-graph transfer: new q-base families

**Agent 9, 2026-11-06.** This intermediate dossier documents a reusable original-source proof method and several previously uncovered necessary critical gateway classes. None decides P1, another six-state machine, or the global BB(6) bound.

## The actual mathematical theorem

For the source authentic P1 accelerated blank reachability `BB6.Agent1.Reach 2`, let `H(n)=14·2^n−2n−10`. The central checked theorem [UniformUniversalCylinder.lean](../agent9-p1-q33/UniformUniversalCylinder.lean), `BB6.Agent9UniformUniversal.universal_blank_critical_cylinder`, takes **any** base `q0≥29` and two lists of exact scalar shadow states closed under *every* edge

`z=2^t v, 2z'+1=16q0+h+m+t+v, m'=m+t+1`, h=8 or 9.

If the lists include the original two roots `(0,12q0+4)`, `(0,10q0+4)`, have all costs `m≤41`, and every coordinate avoids `1024|z`, the genuine P1 blank orbit avoids the necessary critical `Reach(2,H(16q+2))` for **every** `q=q0+2^51 r`, `r∈ℕ`. The result has no inverse-path length cutoff. Original-source Lean CI [42137852125](https://github.com/FlareZ123/bb6/actions/runs/42137852125) **SUCCEEDED** with standard theorem axioms only.

The argument uses [UniformPrecisionStep.lean](../agent9-p1-q33/UniformPrecisionStep.lean) and [UniformPrecisionPath.lean](../agent9-p1-q33/UniformPrecisionPath.lean) to transport a base closed shadow graph through a high-precision perturbed parameter, with invariant `z=zbase+2^(K+M−m)s`. The new [UniformSourceCone.lean](../agent9-p1-q33/UniformSourceCone.lean) bridges every original P1 odd inverse cone into unrestricted exact shadow reachability, including the actual original inverse step and physical reset semantics. [GenericShadowReach41K.lean](../agent9-p1-q33/GenericShadowReach41K.lean) and [GenericCriticalReach41K.lean](../agent9-p1-q33/GenericCriticalReach41K.lean) close the true blank-root exceptional and even-exit branches. Original source CI [42136910030](https://github.com/FlareZ123/bb6/actions/runs/42136910030) and [42137509040](https://github.com/FlareZ123/bb6/actions/runs/42137509040) **SUCCEEDED**.

## Newly certified source families

| q0 | First n=16q0+2 | Base feeder node counts | Max cost | Strong statement |
| ---: | ---: | ---: | ---: | --- |
| 41 | 658 | 49 / 41 | 25 / 24 | `∀r, ¬Reach 2 (H(16(41+2^51r)+2))` |
| 53 | 850 | 44 / 46 | 19 / 17 | `∀r, ¬Reach 2 (H(16(53+2^51r)+2))` |
| 65 | 1042 | 51 / 35 | 19 / 17 | `∀r, ¬Reach 2 (H(16(65+2^51r)+2))` |

The [q41 generated graph](Q41Finite.lean) and [final source theorem](Q41Final.lean) passed [CI 42138506741](https://github.com/FlareZ123/bb6/actions/runs/42138506741). [Q53Final.lean](Q53Final.lean) and [Q65Final.lean](Q65Final.lean) passed [CI 42138672966](https://github.com/FlareZ123/bb6/actions/runs/42138672966), checked against unchanged original P1 definitions with no `sorryAx`.

The three base q residues are absent from the prior Agent9 700/1024 source gateway census and the twenty additional q modulo4096 classes; the corresponding exact exponents 658,850,1042 were also absent from Agent12's 187 certified modulo65536 list. This is a **repository overlap check**, not a claim of external priority, a whole machine decision, or a meaningful new BB(6) upper bound.

## Parametric high-cost extension

[GenericShadowReachBudget.lean](../agent9-p1-q33/GenericShadowReachBudget.lean) and [GenericCriticalReachBudget.lean](../agent9-p1-q33/GenericCriticalReachBudget.lean) proved original-source source-cone exclusion for an arbitrary budget `B` whenever `29≤q` and `B+13≤15q`; [CI 42139284957](https://github.com/FlareZ123/bb6/actions/runs/42139284957) **SUCCEEDED**. The stronger [UniformUniversalParamK.lean](../agent9-p1-q33/UniformUniversalParamK.lean) now allows an arbitrary dyadic cutoff `K` and budget `B`, provided `B+K+3≤15q0`. Any two exact base feeder invariants then exclude the original-source critical gateway throughout `q=q0+2^(K+B)r`. This is a proof about the unchanged `BB6.Agent1.Reach 2` relation, not a synthetic shadow-only statement.

The corrected [Q70Budget.lean](Q70Budget.lean) and [Q89Budget.lean](Q89Budget.lean) both passed the end-to-end original-source Lean workflow [CI 42253385501](https://github.com/FlareZ123/bb6/actions/runs/42253385501), including the generic bridge, finite graph closure, budget bounds, and axiom audit. The exact families are:

| q0 | K | B | Feeder nodes | Max costs | q cylinder | Critical index n |
| ---: | ---: | ---: | ---: | ---: | --- | --- |
| 70 | 10 | 57 | 195 / 199 | 57 / 56 | `q=70+2^67 r` | `n=1122+2^71 r` |
| 89 | 11 | 51 | 258 / 280 | 51 / 50 | `q=89+2^62 r` | `n=1426+2^66 r` |

For q=70, every base shadow coordinate avoids `1024∣z`. For q=89, the h=8 feeder contains a coordinate equal to 1024, so K=10 would be invalid; the checked K=11 certificate instead proves `¬2048∣z` throughout both closures. The exponent shifts are exactly K+B, and the source inequality is checked for both bases.

The q=70 and q=89 residues are absent from the inspected repository census lists `DensityCount695`, `DensityCount700`, and the twenty new q classes in `DensityCount2820`; their corresponding base indices 1122 and 1426 were also absent from the inspected Agent12 187-class source list. This is an internal overlap audit, not a claim of external priority. These are two additional infinite **necessary critical-gateway exclusions**. They do not decide the P1 machine, eliminate its other halting mechanisms, or establish a BB(6) upper bound.

## Research value and limitations

The key reusable contribution is the **finite fixed-base shadow graph → infinite genuine-original-blank-root critical cylinder** transfer, proved for unrestricted finite inverse path length. This permits automatic reuse of fixed-q graphs without explicitly constructing enormous parameter-dependent affine graphs. The cost-parametric extension, if fully validated, handles cases inaccessible to the old universal cost≤41 source proof.

This method only excludes necessary P1 halting gateways within sparse q cylinders. The remaining P1 gate sectors, the true blank-root nonhalting or halting question, a complete six-state coverage proof, and exact BB(6) remain open. Agent9's previously source-proved adaptive q33+2^40r family is stronger on that one base than the uniform +2^51r transfer, and is not superseded.
