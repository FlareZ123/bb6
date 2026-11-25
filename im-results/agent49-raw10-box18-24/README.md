# Raw10 base34 rectangles 18–24: complete candidate partition

Seven exact domain rectangles, each with 7,500 total completions, are covered by an exhaustive first-hole proof tree. The candidate common weighted bound is 598 (ordinary maximum 592 transitions, plus halt and at most five initial blank-delay steps). This is a local coverage reduction, not a determination of BB(6).

Fixed encoded rows: `[8,a,11,6,17,13,11,-1,2,23,-1,-1]` with `a = 19,18,17,8,6,3,2` respectively. D1 and F1 are unrestricted; F0 ranges over `[0,2,4,11,12,14,15,16,19,20,22,24]`. Zero is a genuine halt and minus one a generator hole. The original-source consumer checks these exact domains against raw10Remainder indices 18–24, then offers a pointwise residual reduction without removing any other rectangle.

The search exhaustively branches over allowed ordinary actions, bounds the genuine halt at each first hole, uses translated half-line cycles and local-window invariants, and uses the last-hole theorem when all other instructions are assigned. The sole branch that survives the initial 200-step/certificate search reaches its last hole at 592 (A1=18, F0=20, F1=21). No candidate leaves remain open.

| A1 | Branch nodes | Right cycles | Left cycles | Ngram leaves | Last-hole leaves | Max hole time |
|---:|---:|---:|---:|---:|---:|---:|
| 19 | 8 | 69 | 66 | 14 | 23 | 85 |
| 18 | 8 | 70 | 63 | 14 | 25 | 592 |
| 17 | 8 | 48 | 78 | 19 | 27 | 85 |
| 8 | 9 | 55 | 89 | 20 | 31 | 85 |
| 6 | 8 | 66 | 68 | 14 | 24 | 85 |
| 3 | 9 | 81 | 71 | 14 | 29 | 85 |
| 2 | 8 | 69 | 66 | 14 | 23 | 85 |

## Reproduction and acceptance status

Archive SHA256: `4953030d5ed1231349228a856045dc8eaf37cc69d476c3a937006fb6a3856e55`. Unpack source.tar.xz into a generated directory and run python3 generate.py there. Build Box18to24Source.lean using the existing repository dependency closure. The archive contains only source and generator, no fixture axioms. All seven generated modules passed local Lean 4.36.0-rc2 checks against an executable interface fixture, including individual kernel checks for every leaf and branch; the first monolithic check was memory-limited, so proofs are composed per node. The fixture deliberately axiomatizes upstream semantic interfaces; **this is not original-source proof acceptance**. The full source consumer, exact index identity, and upstream axiom profile must pass CI before counting these boxes as certified. GitHub clone DNS resolution was unavailable in the local environment.
