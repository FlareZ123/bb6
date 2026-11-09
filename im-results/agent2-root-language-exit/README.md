# Cryptid D: first regular-language exits of four blank-derived arithmetic seeds

**Status: Lean-kernel-checked arithmetic-model result, not a new original-source blank-orbit theorem.** Exact BB(6), even the original D machine's eventual halting status, remains unknown. The existing [Agent 37 word-level programme](../agent37-root-language-pilot/README.md) and genuine-root original-source reentries from Agent 35 and Agent 37 predate this computation. The purpose of this dossier is to make the first common, root-directed *unclosed section interface* reproducible, and to identify its immediate source-verified exits.

## Mathematical object and exact statement

For the D machine `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`, use the prepared physically blank-left F/0 regular section
`L(a,q,b)=I_a((01)^q1^b)`, with `a≥2`, `q≥1` and `b≥0`; the canonical `q=0` case has `b=0`.

`DRegularFirstExit.lean` defines an explicit total arithmetic successor `step : S → Option S` using the B, A and E branch table in Agent 37's already source-connected eleven-row model. It returns `none` for the E sector `a≡1 (mod 3), q≥1,b=1`, which is a **regular-language exit**, not a machine halt. It takes care to absorb the trailing `b` ones into the unary count for B with `q=1`, so physically identical tapes share a canonical state.

Let `run n (some s)` iterate the arithmetic partial successor `n` times. The standalone Lean kernel proves the following four exception certificates; each reported index is the **input section**, beginning at index zero. The succeeding abstract `step` returns `none`.

| Canonical starting section | First exception index | `a mod 243` | `q` | `b` | `a` bit length | Next prepared packet |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| `I_5` | 1,711 | 211 | 5 | 1 | 2,424 | `M(8k+5,0,10;0 1^6)` |
| `I_9` | 8,394 | 157 | 6 | 1 | 11,882 | `M(8k+5,0,12;0 1^6)` |
| `I_15` | 9,458 | 121 | 9 | 1 | 13,388 | `M(8k+5,0,18;0 1^6)` |
| `I_39` | 7,611 | 46 | 7 | 1 | 10,776 | `M(8k+5,0,14;0 1^6)` |

In each row `a=3k+4` at the exception input. Lean also proves **every preceding arithmetic section remains in the regular domain** via an arbitrary-time prefix theorem `no_early_exit` and the four individual `seed*_prior` theorems. This avoids presenting a finite sample or empirical last-row observation as a quantified earlier-exit certificate. The numeric `seed*_exception` and `seed*_exit` statements use `by decide` and have **no axioms**. `seed*_prior` depends only on `propext`; local Lean 4.36.0-rc2 completed all checks. The kernel does *not* prove that this arithmetic model faithfully describes all true blank-origin physical returns.

The separate `check_first_regular_exit.py` independently represents each state as its full canonical finite binary word, imports the existing Agent 37 `macro_engine.py`, and compares every model transition through each reported first exit. It checks that the actual next **word-level macro** is precisely `0 1^(2q) 0 1^6`, and records reproducible SHA-256 digests of the section sequences. Agreement provides an interpreter cross-check, not an additional original-source machine proof.

## Immediate exit closures and provenance boundary

For the first three rows, the displayed packet has `p=10,12,18`; all satisfy `p mod 3 ∈ {0,1}`. The existing **original six-state source-certified** theorem [Agent2 PacketSafeReentry.all_safe_packets_regular](../agent2-packet-shift/README.md) therefore gives a designated finite reentry into regular `L`, for each packet and arbitrary unary length `a≥4`. This supplies an exact source family for the *prepared packet*; applying it to the computed blank-derived sequence remains conditional on lifting the intervening arithmetic model to the actual blank trajectory.

For the fourth row `a mod 243=46`, so the post-E packet unary length `8k+5 ≡36 (mod 81)` is divisible by three. It is an **A-terminal**, with packet `M(3u+3,0,14;0 1^6)`. The pre-existing all-parameter, source-verified [Agent35 APacketGeneral.source_a_packet_regular](../agent35-d-sixth-rejoin/APacketGeneral.lean) applies directly with `q=0,r=4`: the prepared packet returns to `L(8u+43,3,2)`. Its exact primitive duration specializes to `12u²+145u+474`, including four `111` tokens and the terminal `110111`. An independent literal 12-rule six-state interpreter checked this duration, full right suffix and physical blank-left first return for `0≤u≤19`; these 20 cases are regression evidence only. This A packet reentry mechanism was already established by Agents 31 and 35 and must not be counted as new mathematical novelty.

These results prove that **all four first arithmetic-language exceptions have known prepared, original-source regular reentries**. They do not prove a later exception cannot lead to an F/1 halt or a no-event E3 core, nor do they certify any long authentic blank-root survival interval. The previously source-certified [Agent 37 twelfth blank-root exceptional return](../agent37-d-timing-cocycle/README.md) already handles an instance of the same q=7 A packet mechanism, and should be reused rather than independently re-proving its raw machine path.

## Highest-value outstanding proof

A decisive next contribution is a **single original-source rooted return-chain lifting theorem** connecting each modeled regular branch and the exact positive physical first-return guard, including padding equivalence, to a physically proved blank-start seed. A concise inductive interface would then carry the arithmetic Lean first-exit theorem across all 1,711/8,394/9,458/7,611 modeled steps without repeatedly computing their gigantic unary values in raw-machine Lean.

This is a root-directed bridge to an already-known exception, and **not a complete D-machine invariant**: further excursions through changed markers, E3 no-event alternatives, and halting prefixes still require an unbounded closure theorem. For the current strongest all-suffix E source interface, use [Agent 2's complete F/E first-event dossier](../agent2-e-seam-root/README.md), original-source [CI 42579563004](https://github.com/FlareZ123/bb6/actions/runs/42579563004).

## Reproduction

Compile `DRegularFirstExit.lean` directly with Lean 4.36.0-rc2; it imports `Lean` only. Run `check_first_regular_exit.py` in the repository using Python 3.10+ and the unmodified sibling `agent37-root-language-pilot/macro_engine.py`. The former certifies arithmetic execution and prefix nonexit; the latter compares two independent model encodings. Neither imports original-source physical `Boundary.lean` transitions, so neither should be cited as an original-machine proof.
