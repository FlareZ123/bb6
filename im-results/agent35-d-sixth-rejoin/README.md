# Agent 35: sixth exceptional D-root reentry, original-source proof in progress

**Status (2026-11-04 03:34 UTC):** source-level Lean candidate awaiting manual original-source verification in [Agent 35 workflow](../../.github/workflows/agent35-d-sixth-rejoin.yml). This is intermediate Machine D blank-orbit work, not a holdout decision, an improved Busy Beaver lower bound, or a proof of BB(6).

## Exact mathematical target

Original six-state binary machine: `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`.
Denote `I_a(Y)` the physically blank-left, F/0 section with right tape `1^aY0^∞`, `P_r=(01)^r`, and `L(a,r,b)=I_a(P_r1^b)`.

The preexisting rooted [Agent25 sixth-exception theorem](../agent25-cryptid-doublezero/BlankSixthExceptional.lean) produces `I_(9t+7)(P_4 1)` from the actual all-blank start and proves the first following E endpoint. Finite **exact arithmetic** evaluation of its `DRegular.run 4494` value indicates `t ≡ 23 (mod 27)`; this must be kernel verified, rather than assumed from a numerical transcript.

For **every** `w≥0`, setting `t=27w+23`, propose the following complete sequence of *designated* F/0 source endpoints:

| Source | Output | Source justification |
| --- | --- | --- |
| `I_(9t+7)(P4 1)` | `I_(24t+13)(0 1^8 0 1^6)` | Agent32 E-double, already rooted |
| `I_(24t+13)(0 1^8 0 1^6)` | `I_(1728w+1505)(P2 0 1^5 0 1^6)` | Agent31 `second_source t 1` |
| `I_(1728w+1505)(P2 0 1^5 0 1^6)` | `I_(4608w+4018)(P1 0 1^5 0 1^6)` | Agent31 source B packet, k=576w+501 |
| `I_(4608w+4018)(P1 0 1^5 0 1^6)` | `I_(12288w+10713)(P3 0 1^2 0 1^6)` | Agent31 source E packet, k=1536w+1338 |
| `I_(12288w+10713)(P3 0 1^2 0 1^6)` | `I_(32768w+28577)(P3 1^2)` | Agent31 `full_A_code_110111_first_return`, k=4096w+3570, token word `[false,false,false]`, tail `111` |

The final output is exactly canonical `L(32768w+28577,3,2)`, a regular grammar reentry after the sixth exceptional event. All time costs in [SixthRejoin.lean](SixthRejoin.lean) use the unchanged original source macro formulas; compositions must transport physical right-blank padding using `BoundaryPadding.ObsEq`.

The modular value `t mod27=23` is essential: generic `k≡1 mod3` E exceptions can remain outside the simple regular grammar after several returns, so the class here is significantly narrower than generic second-return classification.

## Evidence and open obligations

A new proof script `SixthRejoin.lean` contains a universal all-w endpoint composition, the concrete `by decide` root modular guard, and an actual blank-source transport theorem. It has been committed as an **unverified source candidate**. Manual-only workflow `agent35-d-sixth-rejoin.yml` recompiles the pinned original six-state implementation and every upstream theorem, then the new file. Do not call this a verified rooted theorem until workflow completion and a standard-axioms-only audit.

A separate literal-transition regression [check_sixth.cpp](check_sixth.cpp) simulated every primitive step and compared state, head, complete physical blank-left and right-tape content at five endpoints each for w=0 and w=1. The first finished after 178,190,110 steps at unary size 28,577; the second after 821,067,539 steps at unary size 61,345. All ten complete checkpoints matched. The arithmetic identities were independently checked in Python for w=0,1,2,12; the actual symbolic DRegular trajectory was independently evaluated through earlier 8394+1026+2665+10946+4252+4494 regular stages, giving `t6 % 27 = 23`. These are *computational* checks, subordinate to original-source Lean.

A subsequent arithmetic-model probe predicts a further regular-language E exception **34** model returns after `L(32768w+28577,3,2)` for the actual root w, at `q=3,b=1` and `k≡0 mod3`. That next exception may rejoin via preexisting Agent25 `exceptional_EB_general` with p=1. No source theorem currently claimed here for the 34-return suffix.

**Scientific boundary:** a finite authenticated genuine-root return path would establish only further survival of one still-undecided six-state machine, not global nonhalting and not exact BB(6). Results should remain in `im-results/` absent independently established academic originality.
