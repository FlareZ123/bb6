# Complete five-step blank-return nonhalting family: 41,760 cylinders

**Agent 1, 23 November 2026. Status:** exact geometric derivation and exhaustive finite V8 execution, with a stand-alone Node.js reproducer [`enumerate_five_step_blank.cjs`](enumerate_five_step_blank.cjs). The **1,200-member subfamily** was already independently Lean 4.36.0-rc2 source-proved in [successful CI 45251266657](https://github.com/FlareZ123/bb6/actions/runs/45251266657). The present **entire 41,760-family Lean theorem, pairwise-disjointness theorem, and global-frontier graft are not yet kernel-accepted**. The mathematical proofs below are elementary original-machine proofs and are not statistical extrapolation. This is intermediate, not a BB(6) decision or universal bound.

## Exhaustive mathematical construction

Use six ordinary (nonhalting) states `0=A,1,…,5`, two tape symbols, unbounded two-way tape blank everywhere, and one distinguished start state A.

For each:
1. five movement directions `d₀,…,d₄ ∈ {−1,+1}` (32 words);
2. five writes `w₀,…,w₄ ∈ {0,1}` (32 words);
3. four intermediate control states `q₁,…,q₄∈{0,…,5}` (6⁴=1,296 words), with `q₀=q₅=A`;

compute the geometric positions `h₀=0, hᵢ₊₁=hᵢ+dᵢ` and *actual read symbols* `rᵢ` from blank tape by applying each prescribed `wᵢ` at `hᵢ` in order (there is no hypothetical read-zero approximation). Require:

- after the fifth write, **all tape cells are zero**;
- the five *physical input pairs* `(qᵢ,rᵢ)`, for `0≤i<5`, are **distinct**.

For every such record construct the five-row partial machine

```text
(qᵢ,rᵢ) → write wᵢ, move dᵢ, enter qᵢ₊₁       i=0,…,4.
```

Because the inputs are distinct, this is a consistent assignment of exactly five out of 12 transition rows; the other seven rows are wholly arbitrary, including halting actions.

### All-completions nonhalting theorem

**Claim:** every total machine extending any constructed partial table never halts on the all-blank tape.

**Proof.** Determinism and the prescribed actual read symbols force precisely the five given ordinary transitions from the true blank root. Their last state is A, the tape is entirely blank, and the head is at `δ=Σdᵢ`. Five is odd, so `δ∈{−5,−3,−1,+1,+3,+5}`; in particular `δ≠0`. A spatially translated completely blank tape is still a completely blank tape. By translation equivariance of the original two-way Turing machine, the same five instructions execute and reestablish blank-state A with a further head translation by δ. Induction on the number of five-step blocks plus the four intermediate phases proves every finite ordinary step exists, independent of the seven other input rows. ∎

### Pairwise incompatibility theorem

**Claim:** two different constructed partial tables cannot have a common total-machine completion.

**Proof.** Any common completion would have a uniquely determined physical five-step blank-start history. Both specified five-row transition lists purport to be exactly that history, so they prescribe identical input/output pairs at each of the five first-encountered physical instructions. Since every candidate fixes *exactly those five distinct inputs*, the partial tables are identical. Contrapositive: distinct candidate cylinders cannot overlap. ∎

### Exhaustive finite count

A complete deterministic enumeration of `32×32×6⁴=1,327,104` direction/write/state-word combinations, retaining only blank-return geometries with five distinct consulted input rows, yields:

| Net head displacement | Five-row cylinders |
| ---: | ---: |
| −5 | 120 |
| −3 | 3,960 |
| −1 | 16,800 |
| +1 | 16,800 |
| +3 | 3,960 |
| +5 | 120 |
| **Total** | **41,760** |

Exactly **116** of the 1,024 direction/write pairs restore the blank tape after five writes. The other conditions reject repeated consulted input slots; the resulting 41,760 accepted tables are all distinct. The stand-alone reproducer independently simulates *all five physically executed original-machine steps* for every accepted candidate, asserts identical blank-return and first-five consulted inputs, checks uniqueness of partial-table signatures, checks the displacement histogram, and checks that all 1,200 formerly source-accepted five-step cylinders occur in this new census.

Thus the disjoint full-table mass of the five-row family is exactly

```text
41,760 × 25⁷ = 254,882,812,500,000
25¹²             = 59,604,644,775,390,625
family fraction  = 41,760/25⁵ = 0.004276224
                  = 0.4276224% of all raw full tables.
```

This is a cardinality of a defined *nonhalting* raw-table class, not an increase in the best published complete-machine frontier classification. Some other source sound checker may already decide the same full tables.

## Original-source proof interface and frontier relevance

The previously accepted sound primitive-step `finiteTranslatedCheck_sound` theorem (Agent 24, [source](../agent24-translated-cycle/TranslatedFiniteOracle.lean)) turns each `finiteTranslatedCheck p 0 5 = true` into `Cover (DecidedBelow bound) p` for all total completions. The present 41,760 source tables are constructed by the exact same all-tape blank-return schema, so the core missing *formal* task is one `Lean` theorem quantifying the finite geometric parameters and asserting the translated checker accepts exactly those satisfying the two predicates. A full enumeration theorem should additionally certify the 41,760 count and all-pairs incompatibility rather than relying solely on the script.

The **current lasso-only depth-four** physical audit branches on four first unknown inputs and leaves the fifth unassigned. Its older decision oracle checks only finite halts, zero-mask, finite ray, exact finite lasso and entry ray macro; many five-row blank-return tables bypass these. The stronger already established **translated** global audit can decide translated cycles of period ≤4 at depth4, so **do not claim** a 0.4276224% incremental classified mass relative to that audit without proving its exact old-open set for these candidates.

A targeted source gap module for the original 1,200-subfamily is [`FiveStepFrontierGap.lean`](../agent1-five-step-blank-drift/FiveStepFrontierGap.lean); a case-enumeration tactic failed during early compilation, although the finite translated nonhalting theorem itself passed. Formalize that gap and then generalize source certificates to the full 41,760 set, ideally using a parameterized family theorem and `addCertificates` open-set subtraction against the strongest current audit.

This work does **not** determine BB(6), decide an unresolved historical machine, provide a full six-state coverage theorem, or supply a new Busy Beaver lower or upper bound. Its payoff is a sizeable explicit source-nonhalting cylinder class and a reusable simple target for theorem-level global-frontier integration.
