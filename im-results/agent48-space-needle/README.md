# Space Needle research dossier

**Status (7 November 2026): unresolved.** There is no proof that this machine halts or runs forever, and no exact value of BB(6). The strongest current result is an original-source-checked equivalence reducing halting to reachability of a sixth-regular terminal-feeder list. Its exponent and blank-root reachability quantifiers remain unbounded.

## Machine and source model

The machine is the six-state, two-symbol Space Needle machine encoded by

`BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD`

in the pinned [Cryptids source file](https://github.com/google-deepmind/cryptids/blob/ced8f9f44f67a167d5ecc03e687b048c67926371/BusyBeaver/BB6/M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD.lean).

The source-checked high-level orbit starts at `N 1`. For a nonterminal counter `d`, write

`d+2 = 2^v(2q+3)`.

One high-level transition sends

`d ↦ d+v+3(q+1)`.

The raw-machine bridge identifies halting with the actual blank-start high-level orbit reaching a state with `d+2=2^K`. Here `ReachN d` means reachability from the genuine blank-tape start. It is not arbitrary predecessor reachability.

The shifted variable `b=d+2) starts at 3. The external 100-million-update computation starts at the first post-start value 6.

## Exact terminal-feeder equation

An immediate transition from `oddTower q v = 2^v(2q+3)-2` to terminal exponent `K` is equivalent to

`E(q,v,K): (2^(v+1)+3)q + 3*2^v + v + 3 = 2^K`.

The source-oriented equivalent form is

`2^v(2q+3)+v+3(q+1)=2^K`.

The exact inverse modules enumerate all natural solutions for a fixed exponent. The open question concerns which of these sources lie on the one genuine blank-start orbit.

## Strongest current result: sixth-linear root criterion

The fifth-linear theorem first gives the unrestricted disjunction

- `(q,v,K)=(61,6,13)`;
- `(q,v,K)=(340282366920822406584691642613415018481,42,171)`;
- or `5v ≤ K+3`.

Both exceptional sources are excluded from the genuine root orbit by the original-source theorem in [SpaceNeedleFifthRoot.lean](SpaceNeedleFifthRoot.lean). See [FIFTH-BOUND.md](FIFTH-BOUND.md).

The sixth-linear refinement proves that every fifth-regular terminal source satisfies

- `(q,v,K)=(214,3,12)`;
- `(q,v,K)=(62600,5,22)`;
- or `6v ≤ K+4`.

The two new exceptional source counters are 3446 and 4006494. Exact reverse checks exclude both from `ReachN`.

The resulting source-level theorem is [raw_halts_iff_reaches_sixth_regular](NeedleSixthRoot.lean):

`IsHalt target ↔ ∃ k q v, ReachN (oddTower q v) ∧ (v,q) ∈ NeedleSixthRegular.parents (k+1)`.

The exact list specification says membership in `parents(K)` is equivalent to `E(q,v,K) ∧ 6v ≤ K+4`. The source file uses `K=k+1`. Thus every possible halt must enter the actual blank-start orbit through a sixth-regular feeder. The remaining exponent and reachability quantifiers are still unbounded.

The detailed derivation and exception audit are in [SIXTH-BOUND.md](SIXTH-BOUND.md). The complete manual original-source workflow passed in [CI run 42374851305](https://github.com/FlareZ123/bb6/actions/runs/42374851305). It compiles the fifth-root bridge, sixth-linear arithmetic, exact inverse list, root exclusions, and modular obstruction module against the pinned Cryptids source.

## Modular terminal-feeder exclusions

The current Lean source explicitly proves these ten infinite valuation progressions impossible for terminal feeders:

| Valuation class | Source module |
|---|---|
| `v ≡ 4 (mod 20)` | [SpaceNeedleClosed.lean](SpaceNeedleClosed.lean) |
| `v ≡ 19 (mod 21)` | [SpaceNeedleClosed.lean](SpaceNeedleClosed.lean) |
| `v ≡ 62 (mod 110)` | [SpaceNeedleObstructionFamilies.lean](SpaceNeedleObstructionFamilies.lean) |
| `v ≡ 21 (mod 156)` | [SpaceNeedleObstructionFamilies.lean](SpaceNeedleObstructionFamilies.lean) |
| `v ≡ 201 (mod 342)` | [SpaceNeedleObstructionFamilies.lean](SpaceNeedleObstructionFamilies.lean) |
| `v ≡ 74 (mod 812)` | [SpaceNeedleObstructionFamilies.lean](SpaceNeedleObstructionFamilies.lean) |
| `v ≡ 7 (mod 21)` | [SpaceNeedleObstructionFamilies.lean](SpaceNeedleObstructionFamilies.lean) |
| `v ≡ 9 (mod 3081)` | [SpaceNeedleObstructionFamilies.lean](SpaceNeedleObstructionFamilies.lean) |
| `v ≡ 48 (mod 3081)` | [SpaceNeedleObstructionFamilies.lean](SpaceNeedleObstructionFamilies.lean) |
| `v ≡ 59 (mod 5253)` | [SpaceNeedleObstructionFamilies.lean](SpaceNeedleObstructionFamilies.lean) |

The same source-checked module proves finite composite-CRT exclusions at `v=7,12,18,28,35,36`. The v=35 proof's exponent-one simplification was repaired before the successful run 42374851305. The older 100M report documents the first four progressions; later Lean modules extend the explicit source-checked inventory to ten. Candidate progressions discovered by [find_modular_progressions.py](find_modular_progressions.py) remain computational candidates until formalized.

## Odd blocks and a modular negative control

For a run of `t≥1` consecutive odd transitions beginning at `d=2^t m-1`, reaching terminal counter `2^K-2` is equivalent to `5^t m=2^K-1`. Consequently,

`4*5^(t-1) | K`.

This exact all-length odd-block order theorem is source-checked in [CI run 41935571573](https://github.com/FlareZ123/bb6/actions/runs/41935571573). It gives a necessary condition on the final odd block. It does not address an arbitrary even tail before halting.

The source-lifted [terminal-residue family](SpaceNeedleTerminalResidues.lean) proves that every residue class modulo 10 contains arbitrarily large terminal exponents with at least one incoming high-level edge. The two constructions use `K=4(n+1)` and `K=3669+4098n`. These edges are not shown to be blank-root reachable. The result rules out a simple exponent-mod-10 obstruction as a route to global nonhalting.

## Finite computation

The external [100-million-update report](../../resources/2026-11-07-space-needle-100m.md) records:

- 100,000,000 high-level updates from `b=6`, checking all 100,000,001 resulting positions;
- no power of two in the checked range;
- maximum observed `ν₂(b)=25`, first attained at term position 23,145,881;
- final term length 94,125,050 bits;
- 400 checkpoints, matched by a block-affine re-derivation, plus 13 valuation-record events;
- checkpoint CSV SHA-256 `2dd4c88d169f5db331598d49a7773504a18f6dd621d15482f9b497915adb3169`.

The external [final integer hash record](https://github.com/oohzaim1-afk/space-needle-100M/blob/96e50a6ad829fa43e4ecfdf881b6679e599ef0b4/data/final_term_100M.sha256) preserves the final value's checksum. This computation is finite evidence only.

## Main artifacts

- [SpaceNeedleClosed.lean](SpaceNeedleClosed.lean): original high-level counter dynamics and exact transition identities.
- [SpaceNeedleRawBridge.lean](SpaceNeedleRawBridge.lean): raw-machine halting bridge and genuine blank-start reachability.
- [SpaceNeedleFifthRoot.lean](SpaceNeedleFifthRoot.lean): fifth-linear root reduction and exclusion of its two exceptional feeders.
- [FifthHigh.lean](FifthHigh.lean), [NeedleQuinticRegular.lean](NeedleQuinticRegular.lean): fifth-linear bound and exact inverse list.
- [SixthHigh.lean](SixthHigh.lean), [SixthNear.lean](SixthNear.lean): sixth-linear high/near split and finite near table.
- [NeedleSixthRegular.lean](NeedleSixthRegular.lean), [NeedleSixthRoot.lean](NeedleSixthRoot.lean): exact sixth-regular list and authentic-root criterion.
- [SpaceNeedleObstructionFamilies.lean](SpaceNeedleObstructionFamilies.lean): periodic and finite CRT exclusions.
- [TerminalOddInverse.lean](TerminalOddInverse.lean), [FiveAdicOrderFull.lean](FiveAdicOrderFull.lean), [FiveAdicOrderSource.lean](FiveAdicOrderSource.lean): all-length odd-block order.
- [TerminalResiduesArithmetic.lean](TerminalResiduesArithmetic.lean), [SpaceNeedleTerminalResidues.lean](SpaceNeedleTerminalResidues.lean): predecessor families across all exponent residues modulo 10.
- [Root decision implementation](../agent20-needle-coprime/NeedleRootDecisionSource.lean): exact per-target blank-root reachability.

A fixed odd-modulus invariant that forgets the true valuation is necessarily trivial; the exact relaxation and proof are in [MODULAR-ABSTRACTION.md](MODULAR-ABSTRACTION.md).

## Next research priority

Prove that `ReachN` avoids every member of the unbounded sixth-regular feeder family, or produce an actual reachable feeder. Prioritize a history-sensitive root invariant, symbolic reverse-cone closure, or a combined odd-block/even-tail analysis. Further synthetic slope improvements are secondary unless they eliminate an infinite sector of the remaining root existential.

**No exact BB(6) value or Space Needle halting decision is claimed.**
