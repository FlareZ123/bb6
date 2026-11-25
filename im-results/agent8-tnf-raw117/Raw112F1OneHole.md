# Raw112 E1=1LC: F1=1RB one-hole residual

**Status: intermediate empirical structure only. No nonhalting theorem has been established for this residual.**

Exact partial table:

`1RB0RF_1RC0LB_0RD0LB_1LD1RE_0RA1LC_---1RB`

The sole undefined transition is F/0. The goal is to prove it is never queried, which would establish `NeverHalts` for every compatible completion and close one of the two leaves in Agent47's 100,000-bound raw112 parent audit.

## Shared canonical counter grammar

A compact zipper simulation of this residual for 10,000,000 transitions found 371 canonical boundary configurations. Each representative has:

- control state C;
- current symbol 0;
- left word exactly `1`;
- right word
  `00 · (110000)^n · 001111 · L[n mod 6] · H[floor(n/3)]`.

The observed low 12-bit codes are:

| n mod 6 | L |
|---:|---|
| 0 | `110000000000` |
| 1 | `000000111111` |
| 2 | `111110111111` |
| 3 | `110011000001` |
| 4 | `000001111111` |
| 5 | `111111111111` |

The high suffix is a list of five-bit blocks. Its observed recursive base-6 encoding is exactly the same as the encoding found independently for the sibling F1=0LE residual in [Agent19's analysis](../agent19-raw112-residual/analysis.md):

- Base words H(0),...,H(5):
  - H(0) = ε
  - H(1) = `11111`
  - H(2) = `00001 11111`
  - H(3) = `11100 00001 11111`
  - H(4) = `00111 11101 11111`
  - H(5) = `11111 11101 11111`
- For k=6m+r:
  `H(k) = P[r, m mod 2] ++ H(m)`,
  with the same 6×2 three-block prefix table in Agent19's analysis.

I ran both residuals independently for 10,000,000 transitions and compared the canonical suffixes bit-for-bit. They agree for every common n=1..363 (the F1=0LE run reached n=363; F1=1RB reached n=371). There were zero suffix mismatches. Thus the counter *encoding* is shared in the observed range; the macro transition paths and costs are different.

First canonical step counts:
- F1=1RB: n=1..6 at 376, 762, 1,376, 2,108, 2,926, 3,996.
- F1=0LE: n=1..6 at 382, 780, 1,414, 2,170, 3,018, 4,124.

## Observed macro-cost recurrence (conjectural)

For the F1=1RB trace, the exact step difference from canonical C(n) to C(n+1) was extracted for every n=1..370. All 370 costs fit the following recursive function F:

- F(6q+0) = 326
- F(6q+1) = 350 if q is even, otherwise 344
- F(6q+2) = 378 if q is even, otherwise 372
- F(6q+3) = 338
- F(6q+4) = 320
- F(6q+5) = 416 if q=0; 440 if q=1; 468 if q=2; otherwise F(q)+90.

The observed macro cost is:

- 144n+312 if n mod 6=0;
- 144n+242 if n mod 6=1 or 4;
- 144n+300 if n mod 6=3;
- 144n+F(floor(n/3)) if n mod 6=2 or 5.

The recursive branch is well-founded because q<6q+5, and F is positive. This is a concrete candidate for the Lean run0 macro theorem: prove C(n) reaches C(n+1) in this many steps. The formula is currently an experimentally verified conjecture, not a proof of the macro relation. Raw112F1OneHoleTrace.py now checks all observed adjacent costs against it.

## Safety observations

A separate five-million-step run recorded 103,411 visits to F, all reading 1. The reproducibility workflow [CI 45592021140](https://github.com/FlareZ123/bb6/actions/runs/45592021140) then reran both sibling simulators for 10,000,000 transitions: this residual recorded 207,216 F visits, no undefined transition, and zero A/1 visits with a 0 immediately to the right. Since A/1 is the only transition entering F, that is the immediate local condition relevant to F/0 reachability. The same workflow compared the two CSV traces and verified bit-for-bit equality of the canonical suffix, low code, and high stack for every n=1..363; the F1=1RB run reached n=371 while F1=0LE reached n=363. These are reproducible finite observations, not an infinite-time proof.

## Reproduction

`Raw112F1OneHoleTrace.py` implements the independent zipper simulation, extracts the canonical C-boundary representatives, and checks the observed low-code and recursive high-stack formulas. Default horizon: 10,000,000 transitions. It emits CSV traces; no generated output is committed.

## Proof obligation

Prove for every n that the machine starting from the canonical configuration C(n) reaches C(n+1), with every intermediate F visit reading 1. The shared recursive H grammar is a promising common data representation for both F1 siblings, but the F1=1RB transition (write 1, move right, enter B) requires its own macro simulation. The existing affine multi-block pump search is not a proof strategy for this nested counter.

A targeted finite-automata-reduction SMT search is running on this exact one-hole table:
- [CI 45590877120](https://github.com/FlareZ123/bb6/actions/runs/45590877120): DFA sizes 6–10, 120-second per-size/orientation timeout.
- [CI 45591650061](https://github.com/FlareZ123/bb6/actions/runs/45591650061): DFA sizes 1–5, 60-second per-size/orientation timeout.

The workflow independently checks any candidate against the infinite-tape semantics in Lean. Do not claim a FAR theorem unless that check passes. If no certificate is found, the recursive counter macro remains the next mathematical route.
