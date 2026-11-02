# Agent 35: original-machine coded A-section return and 1100 branch

**Status:** intermediate, directly Lean kernel-checked, independently recompiled against the **unmodified, SHA-verified** original Machine D-start Cryptid sources in [manual CI 41416693685](https://github.com/FlareZ123/bb6/actions/runs/41416693685). These theorems have no `sorryAx`, `admit`, or oracle; `#print axioms` reports only `[propext, Quot.sound]` for the main results. They do not decide blank-tape halting or BB(6).

Target binary six-state machine: `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`.

## The exact semantic bridge

Agent 31's `CryptidBoundary.Cfg` and Agent 25's `CryptidA.Cfg` use the *same 12 raw transitions*, but represent the undefined F-on-1 rule differently. Agent 31 changes the current state from 5 to a frozen terminal state 6, whereas Agent 25 freezes F-on-1 in place as state 5. `ABridgeCode.lean` constructs the exact state map `toA`: identity except any original state 6 is sent to state 5 reading a 1. It proves, universally over **all configurations** and times:

```lean
toA_step (s) : toA (CryptidBoundary.step s) = CryptidA.step (toA s)
toA_run (n) (s) : toA (CryptidBoundary.run n s) = CryptidA.run n (toA s)
```

These are checked against the actual original sources, with no hypothesis about avoiding a halt. The bridge has just the ordinary `propext` axiom. Because `toA` identifies two different halted configurations, it is not globally injective. The lemmas `toA_finish` and `toA_aBoundary_converse` recover **unique unhalted original states** when the target is F-on-0 or A-on-0 respectively. This subtlety matters: assuming a globally injective bridge is false.

## Universally coded A-section return

Notation: `I_n(y)` denotes the original raw F-on-0 section with blank left tape and right unary `1^n y`. `A_m(y)` denotes A scanning zero with left stack `0(10)^m11` and right `y`. All suffixes are arbitrary finite Boolean words with implicit blank extension.

For a *finite Boolean code word* `w`, encode its symbols `false↦10` and `true↦111`. Set `d(w) = #false+4·#true`. Define exact primitive cost recursively: consuming `10` costs 2 steps and increases `m` by 1; consuming `111` costs `6m+41` steps and increases `m` by 4. Write `C(m,w)` for the accumulated cost.

`a_code_return` establishes for **all** `m,w,y`:

```
A_m(Code(w) y) --[C(m,w)]--> A_(m+d(w))(y).
```

`full_A_code` composes this with Agent 31's original-machine F prefix and Agent 25's zero close:

```
I_(3k+3)(0 Code(w) 0 y)
  --[12k²+41k+32+C(4k+3,w)+2(4k+3+d(w))+6]-->
I_(8k+11+2d(w))(y).
```

No special form of `w` is required, so the source theorem supports arbitrary interleavings of `10` pairs and `111` triples, beyond all-`10` or all-`111` families.

## Additional universal 1100 return

`ABridgeTwo.lean` imports the exact original Agent 32 `ePairs_run` and proves the previously uncovered A-boundary word:

```
A_(m+1)(1100 y)
  --[2m+18]-->
I_(2m+3)(0 1^6 y), for every natural m and arbitrary suffix y.
```

The three-step A→E head transition reduces the input to Agent 32's all-m `ePairs m 0 y` class, which provides the exact E→F return. The proof is fully symbolic, independent of enumeration and of the unknown suffix.

Composing with `a_code_return` and Agent 31's F prefix, `full_A_code_double` proves:

```
I_(3k+3)(0 Code(w) 1100 y)
  --[12k²+41k+32+C(4k+3,w)+2(4k+3+d(w))+16]-->
I_(8k+7+2d(w))(0 1^6 y).
```

The `1100` case is the first previously unresolved A branch of a *conditional, computationally generated* blank-origin section itinerary at about the 286th macro stage after the certified `I_27659` section. Each universal theorem is exact and source-proved, but that whole itinerary has **not** been formally composed from the actual blank tape.

## Verification and remaining limitations

- Proofs: [ABridgeCode.lean](./ABridgeCode.lean), [ABridgeTwo.lean](./ABridgeTwo.lean).
- Manual-only CI: [agent35-cryptid-code.yml](../../.github/workflows/agent35-cryptid-code.yml), [successful check 41416693685](https://github.com/FlareZ123/bb6/actions/runs/41416693685) at commit `66f65db66a8eb81e1dc069aba3c083a07820d91b`.
- The workflow restores Agent 31's original `Boundary.lean` and Agent 25's original `TripleUniversal` sources with their existing SHA-verification scripts, compiles Agent 32's unmodified `CryptidSix` and `CryptidPairs`, then checks both Agent 35 modules and prints their axiom dependencies.
- Finite-list raw configurations distinguish an explicit trailing zero from an implicit blank beyond the list; therefore the new explicit-zero theorem cannot be inserted into the genuine *implicit-blank* trajectory by a bare syntactic rewrite. Reuse Agent 31/32's existing `_nil` special cases or prove a separately certified blank-padding semantic equivalence before claiming an end-to-end blank-origin result.
- The present results establish arbitrary finite forward prefixes. They do not show a recurrent infinite invariant, a halt, or any new BB(6) bound. They remain in `im-results/` pending real frontier-level advancement.

## New universal E return on alternating pairs followed by 1100 (source certified)

The previously speculative generalized E-on-(10)^q1100 branch is **now an actual all-parameter Lean theorem**, not a finite-simulation guess. The original-source proof is [EDouble.lean](./EDouble.lean), importing Agent32's unmodified `CryptidPairs.lean` and through it Agent31's exact raw machine.

For every `k,q : Nat` and every arbitrary suffix `ys`:

```
I_(3k+4)(0 (10)^(q+1) 1100 ys)
  --[12k²+49k+64+4q]-->
I_(8k+5)(0 1^(2q+4) 0 1^6 ys).
```

At the E boundary, the left stack is `00(10)^(m+2)11`. The `eDouble_front` proof first consumes the right prefix `(10)^(q+1)1100` and reaches `sweepB m` in exactly `4(q+1)+22` primitive steps, preserving arbitrary `ys`. The subsequent `sweepB_run` adds `2m+3` steps, producing the F-on-zero configuration. Proof decomposition: one-pair explicit base; for larger q, `scan_run` followed by a symbolic sixteen-step A turnaround, `cWalk_run`, and a four-step close. These are exact `run` equalities at the source-machine transition level.

**Independent full unmodified-source Lean CI passed:** [workflow run 41418613418](https://github.com/FlareZ123/bb6/actions/runs/41418613418), compiler Lean 4.36.0-rc2. Axiom audit for `BB6.Agent35.eDouble_front`, `eDouble_run` and `full_E_double` reports **exactly `[propext, Quot.sound]`**, with no `sorryAx`. This theorem closes the first formerly unresolved E word in Agent35's provisional symbolic trace (~8386th accelerated section) but does not prove the entire prior tape trajectory arose from the blank start.

### Open boundary

The remaining crucial goal is a genuinely blank-origin composition of these macros, including implicit-blank versus explicitly written zero at the end of `Cfg` lists. The artificial `List Bool` encoding represents the same physical tape by different finite lists unless trailing-blank equivalence is accounted for. A fully certified raw blank tape trace is stronger evidence than arithmetic continuation of individually valid section formulas. There is no known global halt/nonhalt decision.

## Genuine blank-tape source certificates

These results were compiled through the complete actual blank-tape proof chain, importing the original Agent31/Agent26 Lean sources and, where required, Agent32's universal E-returns and physically sound tape-padding bisimulation.

| Absolute primitive-step time | Exact or physical original-machine checkpoint | Verification |
|---:|---|---|
| 1,187,331,039 | F on zero, \(I_{73761}\), pure unary | [CI 41420196359](https://github.com/FlareZ123/bb6/actions/runs/41420196359) |
| 8,442,192,549 | \(I_{196699}\), pure unary | same |
| 60,030,635,984 | \(I_{524525}(0\,1^6)\) | same |
| 426,871,706,605 | \(I_{1398743}\), pure unary | same |
| 3,035,529,732,856 | \(I_{3729985}\), pure unary | same |
| **21,585,935,003,077** | \(I_{9946621}(0\,1^6)\) | [CI 41420196359](https://github.com/FlareZ123/bb6/actions/runs/41420196359) |
| **153,499,683,790,798** | \(I_{26524321}(01010111)\) with implicit trailing blank | [CI 41420449861](https://github.com/FlareZ123/bb6/actions/runs/41420449861) |
| **1,091,552,640,110,031** | \(I_{70731521}(010101010)\) | [CI 41420683093](https://github.com/FlareZ123/bb6/actions/runs/41420683093) |
| **7,762,150,835,454,696** | \(I_{188617394}(0101010)\) | [CI 41421143137](https://github.com/FlareZ123/bb6/actions/runs/41421143137) |
| **55,197,514,669,381,024** | \(I_{502979722}(01010)\) | same |
| **392,515,651,843,862,508** | \(I_{1341279253}(0\,1^{10})\), **physical-tape equivalence (ObsEq)** | [CI 41421143137](https://github.com/FlareZ123/bb6/actions/runs/41421143137) |

Notation: \(I_n(y)\) is original state F scanning zero, left tape blank, right tape \(1^ny\). Every row is derived from the previously kernel-checked real **blank start** (Agent26's \(I_{27659}\) at step 166,999,736), not assumed as a synthetic input. The first ten new rows are strict equality in Agent31's original finite-list `Cfg` representation; the last row uses Agent32's source-certified observational equality, representing the same infinite blank-extended physical tape. Nonhalting up to the last checkpoint follows from the observed F-on-zero state, because original halting F-on-one goes to frozen state6.

Original Lean:
- [BlankBeyond.lean](./BlankBeyond.lean): six exact genuine blank returns through >21 trillion raw steps.
- [ESixBlank.lean](./ESixBlank.lean): completely source-checked universal E-on-six-ones with genuinely implicit trailing blank, preserving the finite output **without** a fabricated terminal zero; universal exact rule for every k.
- [BlankSixCheckpoint.lean](./BlankSixCheckpoint.lean): combines that theorem to reach >153 trillion steps.
- [BlankTripleCheckpoint.lean](./BlankTripleCheckpoint.lean): composes Agent32's fully general E-on-alternating-pairs and `111` family to cross one quadrillion steps.
- [BlankBContin.lean](./BlankBContin.lean): source-proved universally parametric B branch with one incoming extra 1, two exact blank returns, then Agent32's `full_E_pairs_implicit_blank` observational theorem to reach >392 quadrillion steps.
- Manual CI [agent35-blank-beyond.yml](../../.github/workflows/agent35-blank-beyond.yml) reconstructs all original checksum-pinned sources and checks the actual proof chain. Every named finalized theorem has `#print axioms` containing exactly `[propext, Quot.sound]`, no `sorryAx`. The source semantics and arithmetic were compiled by Lean 4.36.0-rc2; there is no bounded simulation substituting for these macro-composition proofs.

These are finite original-blank-trace certificates and are classified as **intermediate**. The proven physical nonhalting horizon is far smaller than the established Busy Beaver champion lower bound, and no resolution of blank-tape nonhalting or BB(6) follows. Investigate invariant closure on reachable right suffixes and rigorous cross-representation composition, now supported by original-source tape-padding bisimulation.


## Original blank tape beyond 392 quadrillion

[BlankAfterPadding.lean](./BlankAfterPadding.lean) uses Agent32's source-certified all-time physical tape bisimulation `source_congr` to compose the preceding observational blank section with Agent32's exact original-machine `full_E_three` return. The resulting source theorem, for the **actual original blank start**, proves

```text
After 2,791,222,372,148,762,301 primitive steps:
  ObsEq F(left blank, scan 0, right 1^3576744673 01010 1111111).
```

This is a rigorous finite lower bound on the exact D-start Cryptid blank runtime in the original machine, from the real blank, without a fabricated final blank. [Original-source pinned Lean CI 41421482616](https://github.com/FlareZ123/bb6/actions/runs/41421482616) passed, final theorem axiom audit `[propext, Quot.sound]` only. It combines the new and shared universal symbolic rules and has no bounded simulation dependency.

The related [BlankFurther.lean](./BlankFurther.lean) **successfully composes** another E triple-pairs return and proves a finite physical blank checkpoint at **19,848,692,333,528,818,046** primitive steps, with F-on-zero, blank left, and right `1^9537985793 (01)^4 0 1^4`. **Original-source Lean CI [41421823798](https://github.com/FlareZ123/bb6/actions/runs/41421823798) passed**, final theorem `blank19848692333528818046` with exactly `[propext, Quot.sound]` in its axiom audit, no `sorryAx`. Its source-level proof composes the independently proved universal Agent32 `full_E_triple_pairs` through Agent32's physically sound `ObsEq` congruence.

All of these are intermediate formally certified finite prefixes, not any proof that the Cryptid holdout runs forever. **The exact BB(6) remains open.**
