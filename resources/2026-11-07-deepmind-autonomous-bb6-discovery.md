# External source: autonomous AI discovery of BB(6) accelerations

**Retrieved:** 2026-11-07  
**Publication:** Marco Dos Santos, Vivek Veeriah, Alex Havrilla, Andrew Bolt, Goran Zuzic, Satinder Singh, and Tom Zahavy, *At the Limits of Computability: Steps Towards Autonomous AI Discovery on the Busy Beaver Frontier*, arXiv:2610.22603, submitted 2026-10-15.  
**Primary source:** https://arxiv.org/abs/2610.22603  
**Related project:** https://github.com/google-deepmind/cryptids

## Main claims

The paper presents a Gemini-based agentic pipeline that discovers and Lean-formalizes exact Collatz-like macro-transitions for BB(6) holdouts. It reports:

- **11 new BB(6) discoveries** for which the authors provide full, newly discovered accelerations and formal proofs of the acceleration rules. The authors provisionally classify these machines as Cryptids, subject to community acceptance.
- **15 further BB(6) machines** with formal proofs of similar community-known rules or new accelerations.
- A first-stage set of 52 candidate machines with apparent Collatz-like behavior, followed by a second-stage agentic research system that conjectures and proves equivalences among remaining suspects.
- The paper explicitly leaves the halting behavior of the newly formalized Cryptids unresolved. A compact exact acceleration is a reduction to an arithmetic reachability problem, not a halting/nonhalting decision.

The 11 new machine strings in Table 1 are:

1. `1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---1RD`
2. `1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE`
3. `1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE`
4. `1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA`
5. `1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE`
6. `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`
7. `1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA`
8. `1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA`
9. `1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD`
10. `1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE`
11. `1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA`

## Methodological details worth reusing

The pipeline starts from simulated blank-tape traces, compresses finite tape segments into symbol-block exponents, and groups configurations by abstract pattern. It then conjectures piecewise-affine transition rules over the exponents, tests the conjectured code against observed transitions, interactively searches for rare and unobserved edge cases, and formally verifies the completed transition rules in Lean.

The paper emphasizes that extending a raw simulation eventually has diminishing returns: large block exponents make additional macro-transitions increasingly expensive to observe. The conjecturing stage therefore needs explicit treatment of unobserved edge cases, and the formal stage must prove the entire rule rather than extrapolate from finite traces.

A second-stage agentic system is then tasked with finding and proving equivalences for remaining suspects, rewarding compressed higher-level accelerations. This suggests a useful complementary strategy for our repository: derive candidate forward return maps from source traces and counter models, then use our exact inverse grammars and source-level reachability theorems to certify exceptional branches and rule completeness.

## Relation to this repository

The authentic Machine C raw table studied here is:

`1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC` (Suspect 46 / holdout #39).

An exact-string comparison against the paper's 11 new-discovery list shows that this Machine C is not among those 11. The paper therefore supplies **methodological context**, not an imported Machine C acceleration or a proof of its halting status.

The most relevant combination for Machine C is:

1. use trace compression and automated conjecturing to search for a more useful higher-level forward return map for the existing three-counter dynamics;
2. validate every proposed macro-transition on adversarially chosen boundary and exceptional inputs;
3. prove the complete transition rule in Lean against the original machine semantics;
4. use the source-certified inverse grammar and the four-sector full-forced normalizer in this repository to eliminate any proposed terminal configurations whose complete physical predecessor set is forbidden.

The paper's use of the term *Cryptid* is broader than the strict community convention and its provisional classifications are explicitly subject to community acceptance. Do not interpret the paper's 11 discoveries as 11 resolved BB(6) machines or as a value of BB(6).

## Source locations

- Abstract and overview: arXiv page, lines 0–6.
- The 11 new machines and 15 additional formal proofs: Table 1, lines 17–48.
- Candidate counts and discovery pipeline: lines 54–73.
- Piecewise-affine / Collatz-like interpretation: lines 82–96.
- Trace compression and automated conjecturing: lines 100–132.
