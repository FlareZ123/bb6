# Original-source finite-configuration lasso certificates and a read-one residual family

**Status (6 November 2026): intermediate certified mathematics.** This dossier supplies an executable, source-sound all-time nonhalting proof rule in the Agent8 six-state raw-table semantics, integrates it into Agent32's physically valid read-one-aware partial frontier, and certifies 90 pairwise-disjoint read-one-dependent finite-loop families outside the existing six-read-zero-row sufficient-condition census. The exact BB(6) value, genuine hard-root coverage, the global score bound, and the computed mass of the new global frontier remain open.

## The original-source theorem

A six-state machine uses twelve input rows, each with one halt choice or twenty-four ordinary moves. A partial machine may leave rows unassigned, which is distinct from assigning a halt. The blank tape is two-way infinite, the initial state is A, and each successful transition moves the head one cell.

The source file [Agent3FiniteLasso.lean.gz.b64](Agent3FiniteLasso.lean.gz.b64) is a gzip+base64 encoding of `Agent3FiniteLasso.lean` (SHA-256 `84966fde79e909dd47607380577ed9eb50ac014f8bc857824d1cdec770873c10`). It imports the **unmodified** [Agent8 finite-support raw-machine bridge](../agent8-coverage-contract/RayFinite.lean) and [Agent4 sparse cylinder mass](../agent4-coverage-smoke/FrontierMass.lean).

Define `finiteLassoCheck p entry period` by physically executing the assigned partial transitions from blank for `entry` successful moves, then `period` further successful moves, and comparing the two resulting *complete configurations*. Equality compares the control state, integer head location, and the exact set of all marked tape positions. Both list inclusions are checked: repeated writes may create duplicate marked-position entries, which do not affect the underlying infinite tape.

The theorem `finiteLassoCheck_sound` proves, for **every** partial machine `p`, all `entry≥0` and `period>0`, that an accepted check constructs `Cover (DecidedBelow bound) p` for **every** bound and **every** full table completing `p`. The proof uses Agent8's actual `finitePartialRun_sound` at both prefixes, proves equality of the entire infinite tape via `sameFiniteCfg_sound`, and deduces no halt at any future time from a positive exact repeated configuration. No finite exploration cutoff is interpreted as a machine-halting bound.

This nonhalting rule is a standard lasso argument. Agent13 already formalized general full-configuration and finite-tape lasso interfaces in [its separate canonical model](../agent13-coverage/README.md). The contribution here is a fully executable interface against Agent8's existing original-source six-state sparse proof objects, plus its use on the physically encountered **read-one** residual; external methodological novelty is not claimed.

## Twenty genuine read-one-dependent nonhalting cylinders

Choose a state `q` among B,C,D,E,F, an initial direction `d` among left/right, and a marker bit `v` among zero/one. The sparse table has exactly three assigned rows:

| Row | Action |
| --- | --- |
| A/0 | Write 1, move `d`, enter `q` |
| `q`/0 | Write 0, move opposite to `d`, enter A |
| A/1 | Write `v`, move `d`, enter `q` |

Every other row is arbitrary. The blank start writes 1 and returns to A on the marked origin after two ordinary moves. If `v=0`, two additional moves restore the complete blank initial configuration, giving an exact length-four cycle. If `v=1`, the marked A configuration repeats after two additional moves, giving a two-step cycle after a two-step prefix.

Lean theorem `toggleReturnCheck` certifies both alternatives for **all** parameters by finite reduction; `toggleReturnCover` transfers them to every full completion through the original-source all-time lasso theorem. Each cylinder fixes three distinct input slots, so `toggleReturnMass` kernel-checks exactly `25^9 = 3,814,697,265,625` full tables per cylinder. `toggle_compatible_params` proves that overlapping full completions force equal `q,d,v`; therefore the 5×2×2=20 cylinders are pairwise disjoint, covering

```text
20 × 25^9 = 76,293,945,312,500 tables
           = 0.128% of the 25^12 raw full-table universe.
```

The Lean source proof covers all-time behavior, and the parameter disjointness and per-cylinder mass are kernel theorems. The final multiplication across the twenty cylinders is elementary arithmetic applied to those results, not a separate Lean cardinality theorem.

## Exhaustive three-row extension: ninety certified lasso cylinders

The reproducible [generate-lasso90.py](generate-lasso90.py) runs an actual blank-tape sparse DFS. It explores every ordinary move at each *first physically encountered unassigned slot*, allowing at most three distinct assigned input slots and checking complete repeated configurations through 20 successful moves. It selects the ninety resulting genuine three-slot lassos that consult a marked symbol. Its deterministic output `Agent3Lasso90.lean` has SHA-256 `d39796e3bc5f4c93013ab088bf325a79033d906b5e24b9259c8b2e5163082512`.

The original-source Lean file proves `every_triple_lasso` and `every_triple_cover` for **all 90 witnesses** (not just a sample); `every_triple_mass` establishes the exact `25^9` table multiplicity for every one. The exhaustive kernel theorem `all_triples_conflict` checks that any distinct pair prescribes incompatible instructions at some shared assigned input; `all_triples_disjoint` converts this conflict into a theorem excluding any common full-table completion. All these theorems and their axiom prints passed [manual source CI 42304539936](https://github.com/FlareZ123/bb6/actions/runs/42304539936).

Thus the full 90-family union contains exactly **90×25^9 = 343,322,753,906,250** all-time nonhalting full tables, **0.576%** of the full canonical universe. The initial twenty families are a proper *subset* of these ninety and must not be added again.

## Why the read-zero-only census cannot identify these cylinders

The existing [Agent32 six-read-zero-row census](../agent32-zero-prefix-global/README.md) independently counts 143,060,975 of 244,140,625 read-zero-row assignments using a pristine zero-writing cycle, a physically encountered short halt, or a finite-prefix fresh-ray cycle. It leaves all six read-one rows entirely free. For the ten fixed **A/0 and q/0** pairs of the initial twenty-cylinder subfamily, the rooted read-zero trace writes a marker at step one, reverses at step two, and then requires the unknown A/1 transition. Its control cycle is neither all zero-writing nor unidirectional, and no short halt or clean ray is discovered by that restricted sufficient-condition procedure.

The independent [check-lasso-disjoint.cpp](check-lasso-disjoint.cpp) evaluates all **10×25^4 = 3,906,250** read-zero completions for the initial twenty patterns. Its extension [check-lasso90-disjoint.cpp](check-lasso90-disjoint.cpp) independently generates the **ninety** actual three-input read-one lassos from blank, checks that every pair of sparse tables conflicts, and exhausts **90×25^4 = 35,156,250** read-zero completions of their other four rows. Every such completion is open in the zero-row-only sufficient-condition classifier and physically encounters the read-one transition. This independent audit passed [CI 42304865440](https://github.com/FlareZ123/bb6/actions/runs/42304865440).

Combining the independently counted original sufficient family and all ninety disjoint read-one lasso cylinders yields an explicit mathematically justified union of **35,270,318,603,515,625 raw tables**, or **59.173775360%** of all raw transition tables. This union fraction relies on the original independently exhausted C++ census and the new finite-subcube check. It must **not** be called a Lean-kernel-certified numerical report, or equated automatically to the separate proof-carrying global audit's evaluated mass.

## New proof-carrying global search interface

[Agent3LassoFrontier.lean](Agent3LassoFrontier.lean) composes the original finite-halt/finite-ray/zero-tape oracle with `finiteLassoOracle`, which exhaustively searches *bounded witness lengths* while proving all-time nonhalting when it succeeds. Its `lassoPhysicalTraceAudit` branches only on the first unassigned transition encountered on a genuine finite-tape blank-root trace, including symbol-one rows. `globalLassoPhysicalTraceAudit_exhaustive` and `globalLassoPhysicalTraceAudit_conserves` state source-sound certified-or-open coverage and conservation of exactly `25^12` raw tables. The actual numerical report has **not** been evaluated; the proof tree leaves every unsupported branch explicitly open.

The source-integrated manual-only [CI workflow](../../.github/workflows/agent3-finite-lasso.yml) reconstructs and SHA-checks the compressed source, compiles Agent8/4/32's original modules and our two Lean modules using Lean **4.36.0-rc2**, audits theorem axioms, and runs both exhaustive C++ disjointness checks and the generated ninety-family source proof. The original finite-lasso theorem and twenty cylinders passed [source CI 42302400307](https://github.com/FlareZ123/bb6/actions/runs/42302400307); the global frontier and independent census were separately checked in [CI 42303107299](https://github.com/FlareZ123/bb6/actions/runs/42303107299) for Lean, with the expanded C++ stage subject to the next workflow run. All theorem axiom prints contain only standard Lean axioms, with no `sorryAx`.

## Limitation and next useful research

These are simple finitely looping machines, not historical six-state holdouts. Their relative contribution is small, even though they identify a genuine weakness of the zero-row-only enumeration. The next valuable step is to prove a *pointwise original-source correspondence* between the C++ zero-row census and the corresponding Lean oracle, then produce a compositional proof-carrying sparse frontier with lasso, translated-cycle, and fresh-ray certificates. A residual-root attachment or an actual-machine nonhalting decision would be substantially more important than further easy-cylinder mass increases.
