# Blank-origin D-family suffix-language pilot: an almost-closed return grammar

**Status: intermediate mathematical synthesis and reproducible computational evidence. No BB(6) bound, no D-family halting decision, no fully imported Lean theorem for the combined return interpreter.** Agent 37, 2026-11-03.

## Authentic source and question

The exact six-state two-symbol table is `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`, state A=0 through F=5, F/1 undefined. The physically meaningful section `I_n(s)` has state F scanning zero, entire left infinite tape zero, and right infinite tape `1^n s 0^∞`; all finite right strings are identified under padding/removal of terminal zeros. Agent3's original-root certificates reduce all six designated blank starts to unary lengths 5,9,15,39 with exact primitive-step offsets. Agent31/32/35/25/2 have original-source Lean certificates for individual quantified B, A-coded and E return families. This work examines whether their output cases synthesize into a forward closed *blank-reachable* language.

## Nearly closed regular class, reconstructed from existing source-proved macro rules

Let `L(a,q,b)=I_a((01)^q 1^b)` for a≥2, q≥1, b≥0; in the q=0 case take b=0, avoiding duplicate pure unary encodings. The machine's **nonhalting future F/0 endpoint**, at the precisely prescribed raw-step time, falls in the same class except in the E exceptional case `a≡1 mod 3, q≥1, b=1`. This statement is an **algebraic case synthesis of pre-existing quantified source-proved macro families**, checked independently on 2,412 synthetic instances, but the entire synthesis has not been separately compiled as a new Lean theorem. It should be cited as a derived source-connected table with an outstanding formal-composition obligation.

Set `a=3k+2` for B, `a=3k+3` for A, and `a=3k+4` for E. Every row's integer formula is for the exact number of primitive transitions from its input F/0 configuration. Terminal-zero padding is understood physically, never as literal List equality.

| Input branch | Exact output F/0 section | Primitive-step cost |
| --- | --- | --- |
| B, q=0 | `I_(8k+9)` | `12k²+49k+40` |
| B, q≥1 | `I_(8k+10)((01)^(q-1) 1^b)` | `12k²+49k+40` |
| A, q=0 | `I_(8k+11)` | `12k²+49k+44` |
| A, q≥1, `b+1=3r` | `I_(8k+11+2d)` | `P+C+2(m+d)+6` |
| A, q≥1, `b+1=3r+1` | `I_(8k+13+2d)` | `P+C+2(m+d)+10` |
| A, q≥1, `b+1=3r+2` | `I_(8k+7+2d)(0 1^6)` | `P+C+2(m+d)+16` |
| E, q=0 | `I_(8k+5)(0 1^6)` | `12k²+49k+50` |
| E, q≥1, b=0 | `I_(8k+5)(0 1^(2q+6))` | `12k²+49k+50+4q` |
| E, q≥1, b≥2 | `I_(8k+9)((01)^(q+1) 0 1^(b-2))` | `12k²+49k+52+6q` |
| E, q=1, b=1 | `I_(8k+3)(0 1^4 0 101010)` | `12k²+49k+96` |
| E, q≥2, b=1 | `I_(8k+5)(0 1^(2q) 0 1^6)` | `12k²+49k+56+4q` |

For the A rows let `m=4k+3`, `u=q-1`, `d=u+4r`, `P=12k²+41k+32`, `C=2u+r(6(m+u)+41)+12r(r-1)`. These come from `u` copies of token 10 and `r` copies of token 111. A rows with `b+1≡1` use one extra token 10 supplied in part by an *implicit blank*; rows with `b+1≡2` use the pre-proved 1100 exceptional terminal. B q=1 produces a longer pure unary input by absorbing its remaining 1s. The E b=1 outputs have separated nonalternating blocks and generally leave L.

For outputs with a trailing literal zero in the old source theorem, the displayed physical word omits this terminal zero. Existing source-level observational equivalence `Agent32.source_pad/source_congr` (and independently Agent37 raw/zipper physical congruence) is the bridge required to make this exact. Original F/0 endpoint results are sufficient for a finite nonhalt conclusion; the table alone does **not** certify *first* return minimality in every row.

**Source provenance**: `im-results/agent31-cryptid-boundary/README.md` and `Boundary.lean.xz.b64` (B and A prefix); `im-results/agent35-cryptid-code/ABridgeCode.lean` and `ABridgeTwo.lean` (arbitrary mixed A tokens and 1100); `im-results/agent32-cryptid-padding/CodeImplicitNil.lean`, `EZeroPair.lean`, `EAllDouble.lean`, `PaddedApplications.lean` (physical implicit-blank specializations); `im-results/agent32-cryptid-third/CryptidPairs.lean` and `CryptidTriplePairs.lean` (E suffix families). Several of these were previously compiled against full original sources in successful manual CI, as their individual README files record. **Our combined table has no independent end-to-end original-source CI audit.**

## Reproducible numerical investigations and failures

1. An independently authored sparse `Int→Bool` physical-tape interpreter and a separately authored dense-tape C++ interpreter verified the actual four unary starting configurations. Up to 120,000,000 primitive transitions per seed, none halted or had a genuine physically blank-left F/0 section outside L. Some intermediate F/0 visits had nonblank cells left of the head; those are deliberately excluded from the section count.
2. A separate C++ exhaustive first-return test on **98,624** synthetic L inputs with `2≤a≤65,0≤q≤28,0≤b≤54` (q=0 only b=0) found no halt/timeouts within a 300,000-transition per-input cap, 98,036 L-output cases and **588** strict physically blank-left F/0 outputs outside L. All 588 exceptional cases had `a≡1 mod3, q≥1,b=1`. This finite check is not a universal proof, though its exceptions agree with the table.
3. A separately coded arithmetic prediction table was matched against the sparse raw interpreter on **2,412** parameter instances `2≤a≤37,0≤q≤6,0≤b≤10` (canonical q0), with **zero** mismatches in exact primitive transition count and *full physical* right tape after stripping implicit trailing zeros. All eleven table rows were represented. The first attempt found 84 superficial mismatches from terminal literal-zero padding; physical normalization resolved all.
4. The naive assertion L is invariant for **arbitrary synthetic** F0 inputs is **false**. Explicit witness `I_7(011)` is in L (a=7,q=1,b=1) and first returns after **157** raw transitions to `I_11(0 1111 0 101010)`, outside L. This is already consistent with prior Agent2 `ReturnGuard.lean` and Agent32 `EZeroPair.lean`; **not a novel machine decision**. A new local standalone Lean 4.36.0-rc2 replay of the literal table confirms no earlier positive physical F0 return (axiom-free) and the 157-step escaped endpoint (only standard `propext`); it does not replace authentic original-source CI.
5. A conservative symbolic return interpreter using only the above source-proved branches plus previously checked A110111/E110111 special cases completed **20,000** conditional macro steps from *each* of the four authentic unary seeds. Local independent raw samples of **4,897** supported synthetic section starts using eleven branch labels matched its exact time and complete physical endpoint or undefined-entry halt; initial five disagreements were off-by-one **frozen halt** versus **number of successful primitive transitions**, corrected in the interpreter. The 20,000-step compositions are *not Lean-certified actual blank-source traces* and cannot be used as fresh formal lower bounds. Avoid claiming novelty over @-d's existing >2.7 million section computation for the primary D0 blank seed.

## Scientific conclusion and next discriminating question

A small common right-suffix grammar admits a complete **one-future-return** case split using existing universal Turing-machine theorems, with one explicit E exceptional family. The exceptional family is syntactically attainable from the grammar, while its occurrence on any particular true blank orbit requires a separate reachability certificate. Even for the exception, other already proved B/A/E rules may restore an L-like word after additional returns. Hence simply saying “the blank trajectory stays in L” or “the exception is forbidden” would be unjustified.

**Next:** Source-import and prove an explicit Lean combined case theorem for the physical language, including `source_congr` normalization. Generalize to an inductively closed *reachable* language covering the E exception and special packet words, with actual blank-start side conditions on the unary count. Tests should favor falsifiable induction and halt/no-return gaps over further long finite traces. Respect the original-source Actions outage: use local kernel checks with authenticity qualification until an actual runner step succeeds.

No file here belongs in `results/` without an external novelty and outcome assessment.
