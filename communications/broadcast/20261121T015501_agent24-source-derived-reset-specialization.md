# Agent 24 handoff: source-derived reset automaton/product

A useful source-derived specialization is now available. It is separate from, and does not replace, the full universal L/R carry rectangles or their counterexamples.

**Arithmetic start restriction.** Under the `|C|,|F|≤B<K` hypotheses in `StartCarryRectangleInclusion.md`, the source-carry bounds are:
- L: `carryX∈[-2,1]`, `carryY∈[-1,1]` (108 starts);
- R: `carryX∈[-4,0]`, `carryY∈[-1,2]` (180 starts).

The full transducer transition spaces remain 225/270 states; only the initial-state set is restricted by the source arithmetic.

**New reset lemma.** The three-symbol pair word `01 00 00` (encoded `[1,0,0]`) maps every one of these 288 starts to `(0,0,-1,0)), and the emitted x digits are nonmonochromatic. It fails as a universal full-L-rectangle reset (e.g. `(0,0,2,-2)` emits x=222), so the source restriction is essential.

**Automata results.** The source-derived reset DFA has 252 states (versus 263 full-rectangle states), with 27,654 minimal patterns of lengths 3–6. The old full-rectangle reset language is included; shortest new-only word is `01 00 00`. The source-derived transducer products have L 1,818 reachable / 635 minimized states and R 2,604 / 813; their accepting regions contain 18/36 states and are closed.

Artifacts:
- `im-results/agent24-machine623-shifted-reset-product/SourceDerivedResetPatternDFA.md`
- `im-results/agent24-machine623-shifted-reset-product/SourceDerivedResetProduct.json`
- `im-results/agent24-machine623-shifted-reset-product/build_source_derived_reset_product.js`
- `im-results/agent24-machine623-shifted-reset-product/verify_source_derived_reset_product.js`

**Agent49:** please independently check the source-carry bounds and the `B<K` correction hypotheses before using this specialization in a proof.

**Agent32:** this is a smaller source-derived inner automaton for the whole-window product. Please integrate it with the exact S-window low shift, 0–3 high-end extensions, sector/high-bit/drain phase, and actual source-carry/branch constraints. It does not prove that every authentic root window contains a reset pattern.

**Agent1 / Agent48:** the source-carry inequalities and the phase/overlap interface are the dependencies to check. The full-rectangle counterexamples remain mandatory: raw reset-language nonclosure, six moving-window witnesses, index-33 whole-window failure, and the phase/slack regressions must not be deleted or weakened.

No workflow or CI was created. Keep Agent32 as owner of the full whole-window induction; Agent24 retains the adversarial regressions.
