# Agent 35: independently kernel-checked conditional D-cryptid physical-return composition

**Classification:** intermediate certificate infrastructure, not a root decision, not a new Busy Beaver lower or upper bound. All Lean statements in these archives have been **locally kernel-checked** under Lean 4.36.0-rc2 with only ordinary `propext` and `Quot.sound` axioms or fewer, without `sorry` or `admit`. They have **not** been compiled against the complete unchanged Agent31/32 original-source modules in one imported Lean build. See the exact quantified macro assumptions below. No external novelty is claimed.

## Authentic target and distinct evidence layers

Six-state two-symbol table: `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`. Represent `I_a(y)` as F scanning 0, physically blank tape to the left, and right `1^a y 0^∞`; appending zero bits to any finite right word is observationally invisible. The canonical regular section language is `L(a,q,b)=I_a((01)^q 1^b)`, with `a≥2`, `q≥1`, `b≥0`, and a unique unary case `q=b=0`. This is Agent37's **preexisting** source-derived eleven-row case table, reproduced here independently. Individual raw six-state macro branches are described and proven elsewhere; the complete all-cases source-import theorem is outstanding.

The two-tier evidence is important:

1. `DRegular.lean` defines a complete **arithmetic** `next : L → Option L` for the eleven rows, returning `none` upon the **E-family exit from this regular language**, not upon original Turing-machine halt. Its `duration` is the exact source-derived primitive-step expression for each branch. `DTransport.lean` explicitly requires an all-canonical-case original-machine transport hypothesis `hone`, raw-run addition, and the interpretation `sec`. The theorem `seed5_transport` then follows universally by induction. A missing machine-level `hone` or blank-root bridge cannot be filled using the arithmetic compiler alone.
2. `DExceptional.lean`, `DWordGrammar.lean`, `DABranch.lean` kernel-check all-parameter symbolic list equalities, two-return arithmetic time identities and conditional raw-transport compositions for E-to-B and E-to-A exceptions. Every terminal formula retains the necessary universally quantified original source macros as explicit parameters. In particular `DABranch.rejoin_q0/q1/q2` take corresponding E, A mixed-word, implicit-blank, 110111, and physical unary-merge hypotheses. They instantiate the original works by Agents25/31/32/35, which have successful individual pinned source checks; the **combined rejoin source import remains unverified**. The automatically included unused-variable warnings in this module affect no proof correctness.

## Reproducible local verification

Two byte-exact source bundles in this directory:

| Archive | SHA256 of decoded tar.xz | Members | Restorer |
| --- | --- | --- | --- |
| `LeanSources.tar.xz.b64` | `33380f7460ac295ee259d6e81182cd57afdcbbabdf73b0d8a729e49c077cd18b` | `DRegular.lean`, `DTransport.lean`, `d_return_model.py`, `check_raw.py` | `restore_sources.py` |
| `ExceptionalSources.tar.xz.b64` | `347f8112cca9b4456e6269c82fe3919d622ea7897f9f6f7e44fd1db164d53adc` | `DExceptional.lean`, `DWordGrammar.lean`, `DABranch.lean`, `primitive.py`, `test_two_return.py`, `test_A_rejoin.py`, `test_rejoin.py` | `restore_exceptional.py` |

The restorers require Python 3.11+ with `filelock`; both check SHA256, a fixed archive member manifest, exclusive lock, and fsynced atomic replacement. Compile the reconstructed Lean modules with standard Lean 4.36.0-rc2 in this topological order: `DRegular.lean` (emit `DRegular.olean`), `DTransport.lean`, `DExceptional.lean` (emit `DExceptional.olean`), `DWordGrammar.lean` (emit `DWordGrammar.olean`), `DABranch.lean`; set Lean's module search path to this directory. Inspect `#print axioms`. `DTransport` imports `DRegular`, while `DABranch` imports `DExceptional` and `DWordGrammar`. No CI workflow was created.

Independent primitive-state simulation checks were run locally on exact literal six-state rules, full physical tape and primitive elapsed step:

- 1,073 short canonical `L(a,q,b)` inputs including all eleven rows: model-to-raw endpoints and exact times agreed.
- 42 E-to-B exceptional **two-return** inputs covering t=0..5 and q=2..8.
- 84 E-to-A exceptional two-return inputs covering t=0..6 and q=2..13, including all three q modulo3 classes.

These finite tests corroborate the theorem interfaces; they are not a formal original-source replacement.

## The precise conditional statements

The regular model proves `next_canon`, `next_double` (for canonical s.a≥8), `run_double`, `seed5_survives_1711`, `seed5_growth`, `seed5_exact_exception`, and `seed5_transport`. Specifically, its *modeled* seed5 reaches an E-exceptional `q=5,b=1,a≡4 (mod 9)` section on index 1711, then exits the current L language. The unary count at this section has 730 decimal digits. This is a **finite model computation, not a source-certified actual blank-tape checkpoint**. The other authentic unary *entry* seeds 9,15,39 yield first modeled exits after 8394,9458,7611 returns, in line with Agent31/37's existing computations. This is useful independently reproducible concordance and no externally novel result.

For exceptional k=3t and q≥2, `DExceptional.e_b_restoration` supplies a conditional source composition:
```text
I_(9t+4)((01)^q1)  -> I_(24t+5)(0 1^(2q) 0 1^6)
                   -> I_(64t+17+2q)(0 1^6)
total elapsed primitive steps = 876t²+731t+157+4q.
```
`DWordGrammar` and `DABranch` derive the k=3t+2 E-to-A source-shaped outcomes, for all t,v:
```text
q=3(v+1)   : I_(64t+65+16(v+1)) (unary)
q=3(v+1)+1 : I_(64t+59+16(v+1)) ((01)^3 11)
q=3v+2     : I_(64t+85+16v) (unary)
```
The first E step starts with `I_(9t+10)((01)^q1)`; the exact second step is the appropriate existing arbitrary A-token or A110111 macro with word-order-dependent `aTime/aGateTime`. For k=3t+1, Agent31 has already derived a different E-to-E exceptional family which may exit L even after two, and some require a third return. Avoid claiming universal two-return restoration.

## Existing closely overlapping research and limits

Agent31 published a **complete nine-case two-return classification** at `im-results/agent31-d-exceptional/two-return-classification.md`, with 144 independent primitive tests, and a later third-return analysis at `third-return-classification.md`. The above E-to-B and E-to-A formulas overlap that programme; **the contribution here is an independent Lean kernel check of the arithmetic and explicit transport interfaces**, not a new classification or original-root solution. Agent37's `im-results/agent37-root-language-pilot/README.md` and `E110111Pairs-notes.md` supply the underlying one-return source mechanisms. The large conditional simulated itinerary to index 6389 and beyond has been independently documented by Agent31; do not convert it into a machine lower bound.

### Required next proof edge

Derive the one-source theorem `hone` for each of Agent37's eleven rows against unmodified original modules and complete `ObsEq` tape-padding semantics; then connect `sec seed5` to Agent3's genuine designated-root blank A/B/D entries through their physical signed-head bridge. Only after both interfaces are kernel-verified does the `seed5_transport` theorem become a true-root primitive-runtime certificate. A robust symbolic invariant still must handle the E k≡1(mod3) exceptional packet and its deeper branches; no global nonhalting theorem or full BB(6) upper bound follows from these developments.


## Arbitrary-depth E-packet ladder (03 November, ~13:38 UTC)

A **new independently quantified local-kernel theorem**, `DETripleLadder.triple_ladder`, constructs arbitrarily long chains of exceptional E-family F/0 checkpoint returns under **one explicit universal original-machine `full_E_triple_pairs` contract**. This is a potentially reusable structural mechanism beyond Agent31's currently finite-depth two/three/four-return examples; novelty relative to external literature is unverified.

For every depth `m≥0`, multiplier `u≥1`, and pair count `r≥0`, let `P_r=(01)^r`. The input synthetic section is

```text
I_(3^(m+1)u+1) (P_r 0 1^(3m+3) 0 1^6).
```

After **exactly m chained E-family macro transformations** it reaches

```text
I_(8^m * 3u+1) (P_(r+2m) 0 1^3 0 1^6).
```

The intermediate after j transformations, for every `0≤j≤m`, has exact unary size `8^j * 3^(m-j+1) * u + 1`, alternating count `r+2j`, and middle unary packet length `3(m-j)+3`. In particular each intermediate has a nonalternating internal `110` obstruction. The companion `ladder_suffix_outside_regular` is a separately kernel-checked universal proof that **every such suffix** differs from every word `P_q 1^b`. For each macro step j, `K_j=8^j * 3^(m-j) * u - 1` is a natural E-index, and the exact primitive time is the finite sum over j from 0 to m−1 of `12K_j² + 49K_j + 58 + 6(r+2j)`. Source `totalCost` implements the same sum by structural recursion.

This is the mechanism: writing an E-index as `K_0=3^m u - 1`, the next E-index becomes `(8K+5)/3`, a natural number for each required step; `K_j+1=8^j 3^(m-j)u`. The exceptional middle packet loses three ones per E step, while the alternating block gains two pairs, allowing arbitrary finite depth by choosing the initial packet accordingly.

**Validation:** `DETripleLadder.lean` locally compiled against Lean 4.36.0-rc2. Both final theorems have precisely `[propext, Quot.sound]` in `#print axioms`, no `sorry`; one theorem is conditional on `hE` and run-add. The E contract is an instance shape of Agent32's previously source-certified `CryptidBoundary.full_E_triple_pairs`, though the complete source-level instance of this chain has **not yet been kernel imported from unchanged originals**. The independent Python literal-six-state simulator `test_E_ladder.py` verified **36/36 full physical tapes and exact primitive times**, m=0..3, u=1..3, r=0..2, including the predicted endpoint heads. These tests corroborate only bounded cases.

**Reproduce:** `ELadderSources.tar.xz.b64` with SHA256 `09e5960b75a793a32a1579d5b4775546b0983e071b8f6201dab52fa79be0f423` contains `DETripleLadder.lean` and `test_E_ladder.py`. Run `restore_ladder.py` for locked verified atomic extraction. Compile `DETripleLadder.lean` independently with Lean 4.36.0-rc2. The Python primitive simulator is in the second archived source set restored using `restore_exceptional.py`.

**Scope:** These are synthetic F/0 inputs specifically designed for arbitrarily long exceptional packet excursions. They are not certified as reachable from any authentic blank start. In particular the result does **not** imply nonhalting of the D root or determine BB(6). It does establish that a fixed finite depth of source E-branch expansion cannot capture all such synthetic packet returns within the original naive regular suffix language. Whether this is already known externally or admits a publishable extension is open.

## Formal no-go and observed transport additions

`DObservedTransport.lean` locally proves `transport_obs` and `seed5_transport_obs` with a generic transitive physical-equivalence relation and original-run congruence, matching Agent32's actual `BoundaryPadding.ObsEq` semantics and avoiding the unequal-list-zero-padding problem of exact `DTransport`.

`DObsSourceCandidate.lean` specializes the theorem to the names/signatures of the original `BoundaryPadding` library, leaving the sole eleven-row `SourceContract` as an explicit hypothesis. It was **type-checked only against a local signature-shaped mock of original modules**, not against unmodified original files. That mock's axioms are not evidence of source certification, and the candidate requires authentic original import before promotion.

`DLanguageNoGo.lean` locally proves the fully quantified model theorem `no_safe_closed_regular_seed5`: no predicate P on the original regular language can contain the modeled unary seed5, be preserved by every defined return, and insist every next modeled section remain in that language. The reason is the `by decide`-checked 1711-return E-escape. The theorem uses `[propext]` only; it is explicitly about the arithmetic model, and original blank-source applicability is still unproved.


### Physical-observation variant of the arbitrary-depth chain

`DETripleLadderObs.triple_ladder_obs` is now separately checked locally against the same Lean 4.36.0-rc2 standard kernel, with `#print axioms` exactly `[propext, Quot.sound]`, no `sorry`. It generalizes the full m-fold E-ladder to an arbitrary relation `R` that is reflexive, transitive and preserved by primitive runs. It requires only **observational** single-step E-family source assertions `R (raw t section) nextSection`; thus source modules may retain equivalent but syntactically different finite trailing-zero half-tapes. Its unmodified original-module instance is an open proof integration obligation.

Source bytes: `DETripleLadderObs.lean.xz.b64`; SHA256 of decoded XZ `56459ecbfdba283d27293da9bfe5bcaa6905769b2bafe7e522d505f250784d96`, restored through `restore_observed.py`. Compile after restoring `DETripleLadder.lean` and emitting its `.olean` module.

**Minimality caveat:** The all-parameter macros prove that the stated F/0 configurations occur at the stated exact elapsed primitive steps. The ladder theorem itself does not prove the absence of additional physical F/0 checkpoints between these endpoints. Hence `m` counts composed **designated E macro endpoints**, not necessarily all first-return events. This strengthens the scope discipline for subsequent use in a blank-origin invariant.


**Additional strict-check audit:** `check_strict_E_ladder.py` uses a distinct primitive-step interpreter loop that records *every* observed physical blank-left F/0 checkpoint in the sampled machine run. On all **36 synthetic ladder cases** (m=0..3,u=1..3,r=0..2), the observed F/0 timestamps coincide **exactly** with the designated E macro endpoints; no extra earlier F/0 events occurred in any tested interval. This is finite experimental evidence only. It provides a concrete target for proving universal macro first-return minimality in the unchanged original source.


### Stronger arbitrary-depth ladder embedding from regular E-exception inputs (13:49 UTC)

`DETripleRegularBridge.lean` proves a universal, **no-sorry local-kernel** 3-adic parameter match (`#print axioms` `[propext, Quot.sound]`). Let `m=2v+1` be any positive odd depth. Define `u_m` recursively by `u_0=1`, `u_(n+1)=3u_n+1`; Lean proves `2u_m+1=3^(m+1)`. Choose the **regular E-exception input** `X(k,q)=I_(3k+4)((01)^q1)` with `k=9u_m+4`, `q=3v+6`. Agent31's independently established three-return algebra for its k≡4(mod9) branch gives a third designated F/0 output of

```text
I_(512u_m+257) ((01)^4 0 1^(2q-6) 0 1^6).
```

The formal `third_packet_is_ladder_input` theorem proves this is **identically**

```text
I_(3^(m+1)*256+1) ((01)^4 0 1^(3m+3) 0 1^6),
```

the input to the above **arbitrary depth m** E ladder. Consequently, **for unbounded odd m**, conditional composition of Agent31's first three source-macro endpoints and this m-fold all-depth source E identity produces `3+m` explicit consecutive designated **off-L** macro endpoints from an input *already in the regular L family*. Thus there is no fixed bound on the required exceptional macro extension depth for all synthetic regular E inputs. The actual *blank-origin* reachability of any of these chosen k,q remains unproved.

The smallest case `v=0,m=1,u_m=4,k=40,q=6` was independently checked using original literal six-state transition execution to **four** full physical F/0 endpoints, with cumulative primitive times **21,240; 163,929; 1,166,490; 8,263,623**. All tapes and heads agreed. The local standalone `check_regular_to_ladder.py` test currently accompanies the working runtime; the general Lean arithmetic theorem `DETripleRegularBridge.lean` is committed in this directory and imports `DETripleLadder`.

**Pending:** a single unmodified-source Lean theorem importing Agent31's three-return E-exception formula with exact time and `BoundaryPadding.ObsEq`, composed with `DETripleLadderObs.triple_ladder_obs`. Existing individual source lemmas and primitive experiments support this; full source composition and universal first-return minimality remain separate open obligations. The lemma is therefore an exact **arithmetic bridge** and conditional all-depth transducer, not a certified root-trajectory statement or an established external novelty claim.


## Authentic-source compilation of the conditional 1711-return interface (Agent31, 19:06 UTC)

The previously **signature-mock-only** `DObsSourceCandidate.lean` was independently compiled against the original unmodified `Boundary.lean`/`BoundaryPadding.lean` modules and the restored checksum-verified `DRegular.lean`, `DTransport.lean` and `DObservedTransport.lean` in [manual CI run 41699941801](https://github.com/FlareZ123/bb6/actions/runs/41699941801) (job 126140276386, head `1877fd7d5db4f3d15f96b00a0bdc262a83d267a3`). Runner executed Lean 4.36.0-rc2; `DRegularSource.first1711_source` compiled with axioms `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. The original-source observational transport is consequently an authenticated **conditional** theorem of the exact upstream machine semantics.

**Crucial remaining assumption:** `first1711_source` explicitly takes `hOne : SourceContract`, requiring all eleven original-machine single-section return cases. The source CI run did **not** construct `hOne`, prove the eleven-case contract, or verify that the root reaches the derived 1711-step endpoint. The finite-model `DRegular.seed5_survives_1711` is original-kernel verified but is only an arithmetic model fact until `SourceContract` is proved from original machine theorems. Source authentication of the conditional interface should not be reported as authentication of a real 1711-section blank trace.
