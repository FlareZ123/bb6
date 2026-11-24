# #429 q0 branch-10 inverse research

**Current state:** the all-parameter problem remains open, but the enormous original counters have been eliminated by a new four-step macro reduction. Every genuinely rooted q0 target forces a length 8u+5 path of a small-counter arithmetic graph from (24u+22,6u+4). The core proof, sound adaptive checker, and million-parameter exclusion compiled locally in Lean 4.36.0-rc2; source adapter compiled against exact extracted original transition and predecessor declarations with standard axioms only. Full-file CI has not been run. See [the main reduction](Q0MacroReduction.md), [core](Q0MacroCore.lean), [checker](Q0MacroCheck.lean), [finite theorem](Q0MacroFinite.lean), and [source adapter](Q0MacroSource.lean).

**Next proof obligation:** uniformly bound all signed paths from the initial ray; the remaining q0 parameters are not resolved by finite scans. Neither the #429 decision nor a BB(6) value is established.

## Supporting structural research

The [quantitative matching-block theorem](Q0CommonBlock.md) strengthens aperiodicity: any square of half-length k in a strict-interior signed path obeys `29*k < 64*t+6144` for terminal rank below `16^t`. The more general arbitrary-depth packing theorem bounds matching blocks at positive rank gap. All three new modules compile against the complete exact signed-model dependency closure; `q0_word_constraint` transfers the bound to every position of the forced q0 path via its Source interface. Arbitrary aperiodic itineraries remain unresolved.

- [Secondary F spine theorem and exact certificate](Q0SecondarySpine.md), [Lean source](Q0SecondarySpine.lean): the first counter after exactly three FSFE blocks satisfies a+3=5461w, exposing the second valuation clock. This proves a fixed-depth pruning limitation even after accelerating the FSFE blocks.
- [FSFE valuation tail](FSFE-valuation-tail.md): corrected competing all-F coordinates, exact all-index block-start form and the surviving branches. The previous mod-128/mod-256 sibling tables were based on incorrect second-coordinate formulas and are withdrawn.
- [Unbounded FSFE candidate blocks](FSFE-2adic-block.md): exact repeated-block algebra and the distinction between syntactic and residue-compatible completed blocks.
- [All-F run and split formulas](Q0-F-run-split.md): initial all-F valuation v2(3u+2), with separate nested sibling clocks. This initial spine differs from the new secondary spine after three blocks.
- [Residue coverage](Q0ResidueCoverage.md): corrected current evidence. Agent 6's [depth-16 computation](../agent6-harmonic429/Q0Depth16InverseSieve.md) leaves 31,376 base classes modulo 2^22 projecting to 13 classes modulo 64. The older 49/64 paper count is withdrawn because the u=26 row was incorrect. The earlier [depth-12 symbolic sieve](Q0Mod4096SymbolicSieve.md) is historical computational evidence with a weaker set of predicates.
- [Concrete u=0 inverse tree](../agent1-429-q0-23-7-inverse-tree.md): pointwise draft, not a uniform cylinder exclusion.


### Exact converse (Agent 6)

[Q0Converse.md](Q0Converse.md): kernel-checked prepared ancestry for every complete signed path, and exact rooted iff reconstructed endpoint is rooted (Source interface). This isolates the global ancestry obstruction and gives a narrow endpoint rank window; no q0 exclusion is implied.
