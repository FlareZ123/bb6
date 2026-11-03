# A universal D0 A110/paired-triple return and a finite-tail grammar obstruction

**Status (Agent 36, 2026-11-03): intermediate source-derived mathematics.** Original rooted BB(6) and D-family halting remain unknown. The individual premises below previously passed original-source CI. The combined `A110TriplePairs.lean` was typechecked against locally signature-matched abstract interfaces; a source-authentic all-import Lean job is pending runner recovery. The independent literal-original-machine `check_a_packet.py` performs exact finite first-return tests. Its successful finite checks are not a universal Lean proof.

## Exact machine and physical configuration

Original D0 six-state two-symbol machine:
`1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`.
A physical `I_a(s)` has state F scanning zero, a blank infinite left tape, and `1^a s 0^infinity` to its right. Explicit trailing zeros of `s` are observationally redundant; leading ones can be absorbed into `a`. All displayed step counts refer to successful primitive transitions until the next stated F/0 configuration.

Let `P_h=(10)^h`, `Q_h=(01)^h`. For every `m,h≥0` and every finite binary right suffix `y`, the source theorem chain implies the **A-boundary return identity**

```text
preA(m, 110 P_h 111 y)
  --[2m + 24 + 6h]-->
I_(2m+5)( Q_(h+2) 0 y ).
```

Proof reduction: Agent37's source-checked `a110_to_E` maps the left-hand A boundary in three transitions exactly to Agent32's `eTriplePairs(m+1,h,y)`. The original-machine `eTriplePairs_run` takes `2(m+1)+6h+19` further transitions to the indicated F/0 endpoint. The arithmetic adds to `2m+24+6h`. This uses the entire arbitrary suffix `y`, rather than merely a finite enumeration.

Further composition with `prefix_A` and Agent25/37's universal mixed `wordCode` consumption gives an exact source-shaped all-parameter F/0 return. Specialize the code to `q` copies of token `10` and `r` copies of token `111`:

```text
I_(3k+3)( 0 (10)^q (111)^r 110 (10)^h 111 y )
  --[12k²+49k+62+4q+12r²+(24k+55+6q)r+6h]-->
I_(8k+11+2q+8r)( (01)^(h+2) 0 y ).
```

This follows directly from earlier source lemmas plus the short A-to-E bridge. The exported source-shaped candidate `A110TriplePairs.lean` contains both universal results as attempted Lean imports, with zero new axioms or `sorry` in that file. The **combined authentic import has not yet executed**; local signature-mock checking cannot replace it. The h=0 case overlaps Agent37's earlier short `110111` theorem, and the h>0 rule is a systematic consequence of Agent32's earlier E-pairs theorem. Thus the mechanism is not claimed as externally novel.

## One-step A closure of the reset-tail packet

Agent31's arbitrary-tail packet notation is `M(a,q,p;Y)=I_a((01)^q 0 1^p Y)`. Set `Y1=01010111`, the tail produced by the E,p=2 reset in Agent31's packet descent. For every `k,q,r≥0`, the three residue cases of `p` give the following **source-derived** F/0 endpoints:

| Input p | Endpoint | Primitive transitions |
|---|---|---|
| `3r` | `I_(8k+12+2q+8r)(010111)` | `12k²+49k+44+4q+12r²+(24k+55+6q)r` |
| `3r+1` | `I_(8k+25+2q+8r)([])` | `12k²+73k+141+10q+12r²+(24k+79+6q)r` |
| `3r+2` | `I_(8k+11+2q+8r)((01)^4)` | `12k²+49k+74+4q+12r²+(24k+55+6q)r` |

The common input is `M(3k+3,q,p;Y1)`. These outputs all belong to Agent37's regular `L` suffix language.

For `p=3r`, consume `q` pair tokens and `r` triple tokens, then close at the zero beginning `Y1`; the remaining `1010111` absorbs one unary one and becomes `010111=(01)^2 11`. For `p=3r+1`, the final single one plus `Y1` is the complete token sequence `(10)^3 111`, closed by an implicit blank zero; the earlier source-certified `full_A_code_implicit_nil` applies. For `p=3r+2`, the final `11 Y1=110(10)^2 111` matches the all-h A-boundary formula above; its terminal zero is a physical blank, leaving the regular suffix `(01)^4`.

This closes the **A-sector reset packet** unconditionally over q,p. It leaves E and B sector boundary transitions to be reconciled and provides no statement that an actual blank-start trajectory ever reaches this synthetic packet family. The strict *first*-return property is independently checked on the finite sample; the source theorem ensures the claimed return occurs at the indicated elapsed time.

## Exact obstruction to the naive two-tail grammar

A natural proposed extension of the regular `L` language is the union with the two packet tails `Y0=0111111` and `Y1=01010111`. This **specific** class is not closed under the original six-state physical return map:

```text
I_4(001010111)  --[50 primitive steps]--> I_5(01111111010111).
```

The input is `M(4,0,0;Y1)`. The output belongs neither to `L` nor to either fixed-tail M family. In fact, every `k≥0` has the source-derived family

```text
I_(3k+4)(001010111)
  --[12k²+49k+50]-->
I_(8k+5)(01111111010111).
```

This is an immediate instance of Agent32's previously source-proved `full_E_pairs(k,0,ys)` with `ys=1010111`, hence a **known-source consequence**, not a new universal source mechanism. Its relevance is as a concrete falsifier for this proposed finite-tail closure. It does not rule out richer finite-tail sets or a larger stateful grammar.

## Verification and remaining work

Run `python check_a_packet.py` to parse all twelve literal machine entries and confirm exact physically blank-left F/0 return times and entire right tapes. It tests:

- 6,750 combinations of the all-h A code branch (k=0..5, q=0..4, r=0..4, h=0..4, nine trailing suffixes).
- 2,430 combinations of the three reset-tail A-sector families (k=0..9, q=0..8, r=0..8, all p residue cases).
- 13 instances of the E counterexample family, k=0..12.

All **9,193** independent raw return checks passed in the investigator's separately executed Python implementation; the committed reproducer uses the same formulas and original literal transition table. Re-run it to reproduce the published count. The program tracks frozen halt separately from primitive successful transitions.

The next meaningful question is whether E/B returns on the new packet suffixes can be represented by a finite guarded tail transducer with a ranking measure across resets. A claimed global D nonhalting proof must also connect that transducer to the genuine original blank root and handle every exceptional boundary. Prior work includes [Agent31 packet descent](../agent31-d-exceptional/packet-descent.md), [Agent37 regular grammar](../agent37-root-language-pilot/README.md) and [Agent35 arbitrary-depth E ladder](../agent35-d-regular-certificate/README.md). GitHub Actions are currently failing before any job steps, so do not claim a new full-source Lean build until a source-matched job actually runs.
