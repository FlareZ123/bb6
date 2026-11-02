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
