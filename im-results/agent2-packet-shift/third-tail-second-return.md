# D cryptid: third-tail second-return synthesis

**Intermediate result.** Original table `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`. Write `I_a(s)` for an F-on-0 configuration with a physically blank infinite left tape and right tape `1^a s 0^∞`. Synthetic inputs are not known to be blank-root reachable.

For all `k≥0,q≥1`, consider `W(k,q)=I_(3k+4)(0(10)^q11010101010)`. The original-source q=1 and q≥2 return lemmas imply, up to physically implicit final zero:

```
W(k,q) --[12k²+49k+76+4q]--> V(k,q)
V(k,q) = I_(8k+5)(0 1^(2q+2) 0 1^14).
```

The original-source first-physical certificates for padded tapes are already checked. New [ThirdTailFirst.lean](ThirdTailFirst.lean) supplies the all-natural physical-blank equivalence and unpadded strict-first transfer. Its generic physical-equivalence lemma was locally Lean-kernel checked. The earlier [CI 42148438364](https://github.com/FlareZ123/bb6/actions/runs/42148438364) compiled only `EThirdTailPhysical.lean`, not `ThirdTailFirst.lean`; full source-import verification of the strict-first transfer is now included in pending run [42360764020](https://github.com/FlareZ123/bb6/actions/runs/42360764020).

## A complete conditional second-boundary table

For `k=3t+d`, use the following additional primitive times from `V(k,q)`. In the d=2 cases write `q=3r+s`.

| Guard | Resulting F/0 endpoint | Additional steps |
|---|---|---|
| d=0 | `I_(64t+19+2q)(0 1^14)` | `768t²+584t+101` |
| d=1 | `I_(64t+33)((01)^2 0 1^(2q-1) 0 1^14)` | `768t²+968t+313` |
| d=2, s=1 | `I_(64t+97+16r)(0 1^6)` | `768t²+2504t+2103+(384t+638)r+48r²` |
| d=2, s=2 | `I_(64t+89+16r)([])` | `768t²+1928t+1216+(384t+494)r+48r²` |
| d=2, s=3 | `I_(64t+75+16r)((01)^2 0 1^11)` | `768t²+1928t+1234+(384t+494)r+48r²` |

The d=0 branch follows the original `full_B`; the d=1 branch follows `full_E_triple_pairs` and remains in packet form `M(64t+33,2,2q-1;0 1^14)`. In d=2 the A-prefix parameter is `K=8t+6` and `m=4K+3`. For s=1 consume `(111)^(2r+1) 10 (111)^4` then finish with the implicit `1100` via `full_A_code_double`. For s=2 consume `(111)^(2r+2)` and close at zero using `full_A_code`. For s=3 consume the same triple code then the `110 111 1^11` portal using `a_110_to_E` and `eTriplePairs_run`. All d=0 and d=2 endpoints belong to the regular L suffix language.

**Evidence:** [ThirdTailArithmetic.lean](ThirdTailArithmetic.lean) locally kernel-checks the full token-cost recurrence and all five polynomial identities, without admitted axioms. [check_third_tail_second.py](check_third_tail_second.py) independently matched exact first and second first-physical times and complete physical tapes for **375 cases** (`k=0..14,q=1..25`), using the literal twelve-transition simulator. The second universal first-event property and an end-to-end original-source import remain open proof obligations. This is a composition of previously established macros, with no original-machine blank-root decision, no BB(6) bound and no external novelty claim.

**Next:** Establish a single source-connected `ObsEq` two-return theorem, then close all exits of the d=1 packet `M(64t+33,2,2q-1;0 1^14)` or show how genuine blank-root history restricts its occurrence.


## Source-composition modules for all second-boundary cases (7 November 2026)

The previous table had a source theorem module for the B/E cases and only the q≡2 (mod3) A case. Two further original-source composition modules have now been added:

- `ThirdTailSecondAOne.lean`: q=3r+1. It applies Agent35's `full_A_code_double` to the special code `111^(2r+1) 10 1111`. The terminal `1100` uses the two physically blank cells after the explicit trailing ones. `BoundaryPadding.source_init_pad` transfers the padded source theorem back to the unpadded physical input. The endpoint is regular L with unary prefix `64t+97+16r` and tail `0 1^6`.
- `ThirdTailSecondAThree.lean`: q=3r+3. It consumes `111^(2r+2)` with `a_code_return`, then composes the original `a_110_triple_pairs_return` portal at q=0 with eleven trailing ones. The endpoint is the F/0 packet with prefix `64t+75+16r`, two `01` pairs, and eleven trailing ones.
- `ThirdTailSecondAZero.lean`: q=3r+2, as previously recorded. It returns to pure unary L.
- `ThirdTailSecondBE.lean`: the d=0 B and d=1 E branches, as previously recorded.

The manual workflow `agent2-packet-shift.yml` has been expanded to restore and compile the original source dependencies for all of these modules, plus `EThirdTailPhysical`, `ThirdTailFirst`, `ThirdTailPositive`, and `ThirdTailArithmetic`. It also records theorem axiom output and rejects `sorryAx` and `_native.native_decide`. Run [42360764020](https://github.com/FlareZ123/bb6/actions/runs/42360764020) is pending. Until it succeeds, the two new A-branch compositions remain proposed source proofs, not CI-certified results.

Even if this CI succeeds, the second-boundary table is a table of exact designated endpoints. It does not establish universal strict-first-return behavior for the second boundary. The d=1 E endpoint and d=2,q=3 A endpoint are new packet families, not regular L closures; their subsequent dynamics remain open.
