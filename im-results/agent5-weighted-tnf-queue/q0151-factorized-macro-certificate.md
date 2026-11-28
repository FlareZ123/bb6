# q0-151: factorized finite macro candidate and source-proof seam

The only target is the q0-151 F0-open partial machine `1RB1LC_1RC0RD_0LA1RD_1RB0RE_1LC1RF_---0RC`. This is **intermediate** work. It is not a root nonhalting proof until the source-level macro/stack interpretation is discharged. The original true run of this machine must be connected to the abstract language independently of the finite checker.

## Exact computational fixed-point structure

Starting with the B-mode blank-root control and restoring **any** globally saved segment on a macro pop (not necessarily the actual stack top), the deterministic Python witness generator `q151_macro_certificate.py` and a separately written JavaScript interpreter both found:

- 814 reachable finite controls (729 B, 85 C).
- 50 saved-segment symbols, including the blank symbol.
- 12 distinct pop-result/right-summary requests.
- 9,935 abstract action edges with the exploratory `a∈{1,2,3}` / `a∈{2,3}` choices.
- No bad action in the proposed finite fixed point; every control has a successor action.

The closed set is exactly the following union of **rectangles**, rather than an unstructured list:

`B×(R₁₇×S₂₈ ∪ R₁₂×S₂₁ ∪ {({emptyRight},{seedSegment})}) ∪ C×(R₁₇×S₅)`.

It has cardinality `17·28 + 12·21 + 1 + 17·5 = 814`. The 12-element right subset is
`[(1,2),(1,3),(1,4),(2,4),(4,2),(4,3),(4,4),(5,3),(5,4),(8,2),(8,3),(8,4)]`.
The 17-element complete right family additionally contains `(0,4),(2,3),(5,2),(6,3),(6,4)`.
A finite control is `(B_or_C,right=(firstRunCategory,suffixMask),segment=(firstRunCategory,imageN,imageP,lastRunCategory))`.
All five C-mode segments have `lastRunCategory=3`, representing exactly three final 1s. The B seed `(B,(0,4),(0,0,1,1))` is exceptional and cannot be multiplied by all right summaries.

These restrictions are **not** a cosmetic compression. Extending B to the full `R₁₇×S₅₀` introduces 121 extra controls. Independent transition checks found 68 escaping stay edges, 51 escaping/missing-symbol push edges and 1,800 escaping pop restoration pairs (with duplicated pairs counted), despite no immediate `.bad` edge. Hence the restricted 12×21 rectangle and exceptional seed matter for closure.

## Kernel-checking design

`Q0151StackSaturation.lean` proves (in a generic push/pop transition system) that a closed finite `Good` control set and a closed `Saved` symbol set preserve safety along every reachable stack execution, including empty-stack pops through a specified blank symbol. This formalizes the liberal overapproximation used by Python.

`Q0151FiniteModel.lean` independently specifies the finite interpreter in Lean, including right suffix masks, segment transfer images, and macro branching. **Lean source CI succeeded**: [run 46131631497](https://github.com/FlareZ123/bb6/actions/runs/46131631497).

`generate_q151_finite.py` now checks the four-rectangle decomposition as an assertion, then generates `Q0151FiniteCertificate.lean`. The generated Lean file computes original finite interpreter transitions on all rectangle rows, checks their membership and nonemptiness, and checks the 12 possible pop-request summaries against all 50 saved symbols. Python **does not** attest to correctness; it only proposes literal lists and theorem statements. **Source-accepted 28 November:** [CI run 46153782229](https://github.com/FlareZ123/bb6/actions/runs/46153782229) compiled all 63 project dependencies, independently regenerated the four-rectangle `Q0151FiniteCertificate.lean` and passed the theorem-suffix audit: `finite_closed`, `finite_progress`, and `abstract_never_bad` each have exactly `[propext]` as transitive Lean axioms; artifact [15266633056](https://github.com/FlareZ123/bb6/actions/runs/46153782229/artifacts/15266633056), ZIP SHA-256 `95dfcdca799d84eaa18d0bf5b30877b580e4ffc9bafcf5dade8a995f0d94b8c7`. The compiler source revision is `a79becccc02855ed652bab57ece97cadd46158e9`. This certifies **only the abstract macro interpreter**, NOT nonhalting of the original Turing machine. The source-closure workflow uses `preparation_profile=q0151-macro`.

## Algebraic and physical-source work

The two-mode DFA's length-one run is an identity transformation. A source-checked Lean theorem `gateRun_insert` in `Q0151ResidueSemantics.lean` proves that arbitrarily many such runs can be inserted in a suffix grammar. `Q0151Category.lean` establishes the finite run-category map `cat(n)=n` for `n≤4`, otherwise `5+(n−1)%4`; the `gateRun_cats` and `gateMask_cats` source audit passed [run 46129923352](https://github.com/FlareZ123/bb6/actions/runs/46129923352). An addition-congruence lemma for merging unfinished and first right runs is under a new audit.

A second independent JS interpreter confirmed the same 814/50/12 closure using only one large-run witness per category, with 5,615 instead of 9,935 abstract edges. Separately, all 729 trial segment summaries with first/last categories 0..8 and transfer images -1,0,1 satisfied `append(append(s,"10"),"10")=append(s,"10")`; 100,000 randomized concrete segment/right words agreed with the abstract right concatenation. These are **tests**, not a general source proof; source-level saturation for arbitrary run lengths remains to be formalized.

The original-table macro lemmas `Q0151SourceMacro.lean` and `Q0151MacroSteps.lean` are already Lean source proofs of strictly positive primitive-step paths. `Q0151PhysicalStack.lean` and `Q0151PhysicalStackMore.lean` transport those macros to physical tapes encoded as `current.reverse ++ 00 ++ savedLeft(stack)`; they cover odd/zero/even and B2 repair cases and are under source audit. `Q0151SegmentGrammar.lean` proves closure of the left segment's scan grammar under append operations, also under audit.

Finally, `Q0151PackedLiveness.lean` gives an actual-machine `Cover NeverHalts` theorem from a source-level region with a positive-length return from each member, accepted in [run 46130063572](https://github.com/FlareZ123/bb6/actions/runs/46130063572). This remains conditional: an invariant relating each concrete physical tape+stack to a `Good` abstract control and a corresponding genuine macro successor must be constructed.

## Remaining decisive work

1. **Done at the abstract level:** the factorized certificate is kernel-accepted without `sorryAx`; the category, concatenation, transfer, scan grammar and all-length source macro components have individual formal proofs, but their full transitive source audit must be verified on the eventual cover root.
2. **Immediate proof target:** `Q0151SourceActions12.lean` adds the previously missing C-mode length-two pop bridge. `Q0151RegionLift.lean` implements a physical stack relation with exact current/saved segment summaries; `Q0151FullCover.lean` assembles exhaustive B/C source-macro cases, including zero-tail physical pops, into a positive-return `Cover NeverHalts p` candidate. These three new files must pass the complete source-closure audit before any nonhalting claim.
3. If the complete original-machine proof is accepted, connect this exact q0-151 open leaf to its authenticated parent and global weighted residual cover; do not decrement the current Canonical38 count without an accepted membership and consumer lineage.

No statement here determines the exact value of BB(6).
