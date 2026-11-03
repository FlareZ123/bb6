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
