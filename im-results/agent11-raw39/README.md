# Raw39: nine accepted child bounds, two remaining canonical obligations

**Status:** locally kernel-checked, artifact-linked conditional parent Cover; not a complete Raw39 Cover or BB(6) upper bound. The first-hole query is A1 at live time 6 for `1RB---_1RC---_0RD---_1LD0RA_------_------`.

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

The previous StableCut/StableIntegrated/SymmetryCut interfaces and Six/Seven/Eight are historical conditional compositions. The accepted 1RE partition is documented in [Raw39RE1Frontier.md](Raw39RE1Frontier.md). The remaining difficult discovery branches are 0LE and 1LE; neither is yet a complete child proof.

## LE discovery frontiers

The exact compressed partitions [0LE](0LE-frontier.json.xz.b64) and [1LE](1LE-frontier.json.xz.b64) retain original normalized open indexing; residual arrays predate the custom proofs below. They are not complete Lean child proofs.

| Branch | Open | FAR | Asym | Run | Block | Run/block | Late | Delayed cycle | Original residual | Remaining |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 0LE | 11603 | 9864 | 1302 | 223 | 143 | 38 | 10 | 14 | 9 | 3 |
| 1LE | 26246 | 23084 | 1790 | 877 | 373 | 34 | 24 | 15 | 49 | 1 |

Candidate weighted bounds 15125/28310, not source-accepted. All 1688 run/block discoveries independently regenerated in Python. Custom Lean proofs checked locally against exact artifact-linked dependencies; only propext and Quot.sound:

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

Remaining 0LE IDs: 1300, 1583, 4084. Remaining 1LE ID: 180. [Exact A-return and rational sweep reduction](Raw391LE180Sections.md) isolates its first undefined query and excludes a finite number of arbitrary-length sweep alternations; it is not yet an inductive invariant. [One-stack pushdown reduction](Raw391LE180PDS.md) gives an exact safety-certificate criterion and a phase-sensitive left-language invariant; no abstraction has closed the leaf. The semantic generator dispatches delayed cycles and 54 custom leaves (locally checked, some source-accepted). Explicit `--conditional` emits `Raw39{0LE,1LE}Conditional`, with named `ResidualHypotheses` fields, a separate manifest, and `all{0LE,1LE}_if_residual`; complete mode refuses any unresolved leaf. A genuine mixed conditional/accepted Raw39 root join was kernel-checked locally, but full LE regeneration and source audit remain pending. No complete parent or universal BB(6) bound.
