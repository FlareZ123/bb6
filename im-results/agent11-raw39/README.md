# Raw39: exact attained score 28311; sole missing 1LE child upper bound

**Established source-level reduction (28 November):** all discovery holdouts are closed and the full original-source Lean join of the **ten already accepted A1 child bounds** has passed [run 46111414686](https://github.com/FlareZ123/bb6/actions/runs/46111414686) (artifact [15248719734](https://github.com/FlareZ123/bb6/actions/runs/46111414686/artifacts/15248719734), SHA-256 `7e0508be348664aac073c9e0aa4b19e7bdea106183fad85e339c8f2fa0b0664d`). Its principal theorem is the exact equivalence `BB6.Agent11Raw39TenChild.parent_bound_iff_oneLE : Bound 28311 p39 ↔ Bound 28311 (child ⟨true,false,4⟩)`, with only standard axioms `[propext, Classical.choice, Quot.sound]`. **The whole Raw39 upper bound is now reduced to the single 1LE child.** The exact weighted 28311 lower witness is separately established. The 1LE all-completions upper bound remains unaccepted, so no complete Raw39 Cover or BB(6) upper bound is claimed. Raw39 is `1RB---_1RC---_0RD---_1LD0RA_------_------`, whose first-hole query is A1 at live time 6.

`Raw39AcceptedNine.lean` proves `BB6.Agent11Raw39AcceptedNine.parent_cover_two`: at every B ≥ 2354, bounds on exactly 0LE and 1LE imply `Cover (WeightedBound B) p39`. It composes the accepted 1RE theorem (weighted bound 1459) with the previous eight-child join, including the original fresh-state symmetry and literal cycle cases. No global roster change has yet been earned.

| A1 move | Weighted bound | Source run | Artifact | Proof source revision |
| --- | ---: | ---: | ---: | --- |
| 1RB | 175 | 45639153728 | 15036330602 | 439ff1526b1d9b19b3e5a02f8c1c764eadcbdbda |
| 0RB | 1271 | 45644271619 | 15039311430 | c39dbcb430765b7d8f630dc7fd7633e613bee8e6 |
| 1RC | 1882 | 45644280485 | 15039350734 | c39dbcb430765b7d8f630dc7fd7633e613bee8e6 |
| 0RE | 944 | 45680199670 | 15054707946 | 9e3bfe908a91b42031d33e46c42b03c71b1a84b1 |
| 0RC | 2354 | 45753648611 | 15087393537 | aa832e9f7734b28505baa8527de0f19979f009ca |
| 0LA | 1003 | 45766252232 | 15091944603 | a82f9d0ca7b85b6dfb2b32e09d6d36c1e8133680 |
| 1LB | 266 | 45796346387 | 15105668345 | 71a9e95c80f388f8889b183cc9474ba3833a10a4 |
| 1LA | 349 | 45796691482 | 15105938864 | 09d6ed0777264e83a08fade7284edf49445bbb57 |
| 1RE | 1459 | 45799903269 | 15109002717 | f24ca0ced242de3e13e71f6cf9cc970fb637340d |

All nine archives were merged locally, verifying the embedded manifest SHA256 for each source and object and byte identity of all duplicated modules. 88+100+102+97+94+232+307+308+539 manifest entries yield 1438 distinct source/object pairs, with zero mismatches. This is a specifically audited legacy object link, not a claim of identical whole source revisions.

Lean 4.36.0-rc2 compiled Raw39AcceptedSix, Seven, Eight and Nine in order against these exact dependencies. Nine's `remaining_count` uses only propext; `parent_bound_two` and `parent_cover_two` depend only on propext, Classical.choice and Quot.sound. Nine source SHA256: eb048a3c0aec74326b4e073c031335b1772d7cfc5f3e107bb702493ce871e4c6. Reproduce by downloading the nine exact artifacts, checking manifest hashes and common module equality, setting LEAN_PATH to the merged directory and compiling the four named modules in order using the same Lean release. This is distinct from a fresh source rebuild.

The previous StableCut/StableIntegrated/SymmetryCut interfaces and Six/Seven/Eight are historical conditional compositions. The accepted 1RE partition is documented in [Raw39RE1Frontier.md](Raw39RE1Frontier.md).

## Exact attained parent score

[Raw39ExactJoin](Raw39ExactJoin.md) gives the exact 28311 attaining witness and excludes 28310. The ten-child theorem `parent_bound_iff_oneLE` now source-accepts the complete parent bound **if and only if** the outstanding 1LE bound holds; [Raw39TenChildPartial.lean](Raw39TenChildPartial.lean) also supplies a conditional parent Cover, exact-threshold theorem and bound lift. Its ten source-certified child artifacts include the accepted 0LE weighted bound 15125 ([CI 46093979153](https://github.com/FlareZ123/bb6/actions/runs/46093979153)). The prior [six-shard corrected-bound run 46094272482](https://github.com/FlareZ123/bb6/actions/runs/46094272482) did not complete g1/g5. The later [16-shard run 46102161614](https://github.com/FlareZ123/bb6/actions/runs/46102161614) source-accepted 15 independent shard jobs but was cancelled at the 45-minute limit for g10, during `Raw391LEAsym75`; these are resource interruptions, not counterexamples. The current five-group 1LE audit [46111417557](https://github.com/FlareZ123/bb6/actions/runs/46111417557) reuses six previously accepted source/object closures and splits the last expensive groups. [Raw39CompleteJoin.lean](Raw39CompleteJoin.lean) and [Raw39Canonical40Bridge.lean](Raw39Canonical40Bridge.lean) remain proposed final consumers pending full 1LE acceptance; the literal Raw39 Canonical40 roster membership [passed CI 46102358966](https://github.com/FlareZ123/bb6/actions/runs/46102358966). The follow-on source audit [CI 46111496271](https://github.com/FlareZ123/bb6/actions/runs/46111496271), artifact [15250336212](https://github.com/FlareZ123/bb6/actions/runs/46111496271/artifacts/15250336212), SHA-256 `fc1fcc5b6c624482385821ec31020177fb33533838c90966d75ff8e90d153cf9`, **accepted the Canonical40 conditional theorem with 39 retained Covers plus the explicit Raw39 parent Cover hypothesis** (`BB6.Agent11Raw39Canonical40Conditional.conditional_exact_at_champion`). This does not discharge the Raw39 Cover or decrement the unconditional global quotient roster.

## LE discovery frontiers

The exact compressed partitions [0LE](0LE-frontier.json.xz.b64) and [1LE](1LE-frontier.json.xz.b64) retain original normalized open indexing; residual arrays predate the custom proofs below. They are not complete Lean child proofs.

| Branch | Open | FAR | Asym | Run | Block | Run/block | Late | Delayed cycle | Original residual | Remaining |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 0LE | 11603 | 9864 | 1302 | 223 | 143 | 38 | 10 | 14 | 9 | 0 |
| 1LE | 26246 | 23084 | 1790 | 877 | 373 | 34 | 24 | 15 | 49 | 0 |

Weighted upper bound 15125 is source-accepted for the complete 0LE child; 28311 remains a candidate complete upper bound for 1LE pending its source audit. The previous 28310 candidate is false because the late 1LE witness admits one incoming blank delay. All 1688 run/block discoveries independently regenerated in Python. Custom Lean proofs checked locally against exact artifact-linked dependencies; standard axioms only:

- [0LE 5883](Raw39LE5883.md): unbounded base-four carry grammar.
- [0LE 1791 and 1800](Raw39LE1791.md): alternating residue-three run-count grammar.
- [0LE 7634](Raw39LE7634.md): complementary modular left runs and right pair grammar, complete unbounded nonhalting proof.
- [1LE 25795,9206,15745](Raw391LEMoreSweep.md): three further exact periodic growth proofs.
- [1LE five periodic D-state variants](Raw391LEFiveSweep.md): arbitrary-repeat proofs with increments 18 and 16.
- [1LE seven further F1 siblings](Raw391LESweeps.md): exact two-block and four-sweep growth certificates.
- [1LE 5774/5781/5789](Raw391LEFTrio.md): common four-sweep growth, complete unbounded proof for three variants.
- [1LE 19021,19049,19091,20727,20938](Raw391LEBinaryFive.md): shared quaternary carry grammar.
- [1LE 1897,2372,2529,2534,2535,2550](Raw391LEBinarySix.md): arbitrary binary tail with growing right sweep.
- [1LE 1837](Raw391LE1837.lean): paired-bit carry, all pairs 00 or 11, entry 61 steps.
- [1LE 2370](Raw391LE2370.lean): single low bit and duplicated high bits, entry 53 steps.

- [1LE 18789,18790,20550](Raw391LEPairTriple.md): paired-one/triple-zero left language and modular right runs, with positive-cost closure for every grammatical configuration.

- [1LE 21614,21623](Raw391LEDriftPair.lean): exact translated left drift, entry 1154/1124, period 2158/2108, fixed inserted 30-bit block before arbitrary tail.

- [1LE 6270,16538](Raw391LEBlockRuns.md): ternary block-run language, with separate end and gap unwinding proofs for arbitrarily many saved runs.
- [1LE 5777/5779/5787](GapListStackGrammar.md): exact four-mode gap/stack reduction and eight-prefix inductive grammar; full artifact-linked local nonhalting theorem for all three, only standard axioms.

- [1LE 8865](Raw391LE8865.md): recursive reset-language proof, source-accepted run 45871946437 / artifact 15141704829.

- [1LE 15741/15742/15743/22215](Raw391LEFourPhase.md): common two-block affine-growth proof, source-accepted run 45873034483.

- [1LE 7080](Raw391LE7080.md): recursive carry-language proof, source-accepted run 45874103755.

- [1LE 12198](Raw391LE12198.md): nested alternating-block grammar; source-accepted run 45875637618.

- [0LE 3414](Raw39LE3414.md): six-phase affine growth; locally kernel-checked against fresh original semantics, exact cost 1252+864n.
- [0LE 3334](Raw39LE3334.md): alternating-gap finite abstraction, 3161 quotient configurations, local kernel proof on exact original checker dependencies.

- [0LE 1300](Raw39LE1300.md): positive-cost returns through two unbounded periodic sweep families, locally kernel-checked.

- [0LE 1583](Raw39LE1583.md): exact arbitrary-tail eight-sweep recurrence, entry 3210 and cost 1028+128n, locally kernel-checked on original dependencies.

The last 0LE discovery holdout 4084 is closed by the [exact arbitrary-tail pump](../agent43-raw39-4084/PACKED-CLOSURE.md): entry 153471, period 15364, growth 18, with 166 kernel-checked packed segments and an unrestricted nonhalting theorem. The [earlier two-stack reduction](Raw39LE4084.md) is superseded as a closure method. The last 1LE discovery holdout, [180](Raw39LE180.md), is closed by a locally kernel-checked native port of the upstream sixteen-block collar-box certificate identified by Agent9. The earlier A-return and pushdown reductions are superseded as closure methods. The semantic generator dispatches delayed cycles and 58 custom leaves (locally checked, some source-accepted). Explicit `--conditional` emits `Raw39{0LE,1LE}Conditional`, with named `ResidualHypotheses` fields, a separate manifest, and `all{0LE,1LE}_if_residual`; complete mode refuses any unresolved leaf. A genuine mixed conditional/accepted Raw39 root join was kernel-checked locally, but full LE regeneration and source audit remain pending. No complete parent or universal BB(6) bound.
