# #746: exact high-band odd image and a 27-adic fatal-depth sieve

**Intermediate source-certified mathematical result, 9 November 2026.** This dossier concerns the original six-state machine `1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA`, with the authenticated source-C first-reset model and blank-origin first reset height 2. The finite and unbounded conclusions below concern actual first-reset *edges* between arbitrary natural heights. They do not establish that a constructed ancestor is reachable from the blank origin. The blank-root halt/nonhalt problem and BB(6) remain open.

## Complete high-band odd-image characterization

Let `K(h)` be the least `k` satisfying `h+k+5 < 8·2^k`, and let `oddPred(e)` abbreviate

```text
∃ a, (a+K(a)) mod 2 = 1  and  bitOutcome(a) = some(e).
```

Here `bitOutcome` is source-proved equal to the original first-reset outcome. For **every** `k=K(e)≥2` and `e≥6·2^k`, the [full original-source Lean theorem](SweepOddFatal27Upper.lean) `entire_high_odd_image_iff` proves the exact equivalence

```text
oddPred(e)  ↔
  if 4e+10 < 27·2^k then 27 | (2e+5)
  else                         9 | (2e+5).
```

The necessity and sufficiency are both exact and unbounded. In the narrow interval, [`narrow_high_odd_output_mod_twentyseven`](SweepOddFatal27Source.lean) excludes valuations `t=0` and `t=1`; [`narrow_high_odd_has_parent`](SweepOddFatal27Band.lean) constructs a genuine `t=2` odd first-reset predecessor whenever the 27-divisibility condition holds. In the complementary upper interval, [`upper_high_odd_has_parent`](SweepOddFatal27Upper.lean) constructs the `t=1` predecessor whenever 9 divides the numerator, and the existing Agent 10 theorem `high_odd_bit_output_mod_nine` supplies necessity.

The complete source odd inverse grammar has `q=2^t d`, `d` odd, `2e+5=3^(t+1)d`, and the exact quotient interval `6·2^j+1≤q≤8·2^j−1` at source index `j`. For `e≥6·2^k`, the `t=0` quotient falls strictly in the empty gap `(4·2^k,6·2^k)`. In the narrow interval `4e+10<27·2^k`, the `t=1` quotient additionally falls in the empty gap `(2·2^k,3·2^k)`. The explicit `t=2` and `t=1` converse quotients land inside the respective exact bands at `j=k−2` and `j=k−1`.

This result classifies odd-predecessor **existence**. It does not assert uniqueness, since additional odd inverse valuations may coexist.

## An exact mod-27 restriction on adjacent fatal histories

Consider an authentic odd first-reset `a→e` into level `k=K(e)`, followed by `m` successful same-level resets and one adjacent even exit into fatal `F_(k+1)=4·2^(k+1)−(k+1)−4`. The earlier source-certified adjacent-fatal theorem supplies the exact deficit identity

```text
e + 2^m·(4k+10) = 8·2^k + k.
```

If the entry lies in the narrower band `e≥6·2^k` and `4e+10<27·2^k`, the new image theorem gives `27 | (2e+5)`, hence

```text
16·2^k+2k+5 ≡ 2^(m+1)·(4k+10)  (mod 27).
```

The [source-connected `narrow_odd_entry_adjacent_fatal_depth_27` theorem](SweepOddFatal27Source.lean) combines this with Agent 10's independent uniform fatal-sector theorem `k mod 6 ∈ {3,4}`. The [arithmetic theorem `fatal_depth_mod27`](SweepOddFatal27Arithmetic.lean) proves the resulting **unique** `m mod 18` class for each `k mod 54`. Periodicity of powers of two modulo 27 reduces the quantified claim to one kernel-checked finite table of 54 × 18 cases.

| `k mod 54` | Required `m mod 18` | `k mod 54` | Required `m mod 18` |
|---:|---:|---:|---:|
| 3 | 5 | 4 | 17 |
| 9 | 3 | 10 | 13 |
| 15 | 1 | 16 | 9 |
| 21 | 17 | 22 | 5 |
| 27 | 15 | 28 | 1 |
| 33 | 13 | 34 | 15 |
| 39 | 11 | 40 | 11 |
| 45 | 9 | 46 | 7 |
| 51 | 7 | 52 | 3 |

Every listed residue also satisfies Agent 10's prior mod-9 table, which selected only one `m mod 6` class for each eligible `k mod 18`. The new proof refines that restriction by a further factor of three in depth congruence, under its explicitly narrower entry hypothesis.

## Concrete synthetic source path

An exact integer example demonstrates that the new interval is inhabited by authentic source edges. Take `k=105`, `m=97`, and

```text
a = 70800633523858145831741793840956
e = 256382333896159396452708223287401
z = 324518553658426726783156020575931
F_106 = 324518553658426726783156020576146.
```

Direct evaluation of the source-equivalent exact arithmetic gives an odd `t=2` first reset `a→e` with `K(a)=103` and `K(e)=105`. It is followed by 97 successful even same-level resets `e→…→z`, then an even reset `z→F_106`; the next source episode halts. The entry satisfies `6·2^105≤e` and `4e+10<27·2^105`, with `k mod 54=51` and `m mod 18=7`, matching the universal table. The finite path was checked by exact integer evaluation; the universal source first-reset and same-level batch rules used by this calculation have separate Lean source proofs. This synthetic starting ancestor has **no demonstrated blank-root reachability**.

## Verification, provenance, and next obstruction

[**Full original-source Lean 4.36.0-rc2 CI run 42593843110**](https://github.com/FlareZ123/bb6/actions/runs/42593843110) succeeded, compiling all four new modules, the unchanged original source-C first-reset and inverse grammar, and the prior Agent 7/10 dependencies. The axiom audits show `propext`, `Quot.sound`, and imported `Classical.choice` only, with no `sorryAx`. The standalone mod-27 arithmetic proof uses only `propext` and `Quot.sound`. The manual workflow is [`agent44-746-fanin.yml`](../../.github/workflows/agent44-746-fanin.yml); it has not been replaced with per-commit automation.

Earlier and distinct source results include [Agent 7's direct-fatal predecessor mod-18/fork classification](../agent7-cascade-forward/FirstFork.lean) and [Agent 10's broader but weaker high-odd-entry mod-9 adjacent-fatal sieve](../agent10-cascade/SWEEP-ODD-FATAL-DEPTH.md). The present exact **high-band image iff** and conditional **mod-27 depth refinement** supply additional tools for those inverse investigations. Earlier direct-fatal mod-18 facts are deliberately not claimed as new.

The remaining decisive unknown is whether any height in these source-compatible families belongs to the *genuine blank-origin forward orbit*. The current theorems strengthen the parent grammar and prune narrow odd-entry fatal histories while leaving that root-sensitive obstacle unresolved. These findings remain under `im-results/`, pending independent assessment of external novelty and academic publishability.
