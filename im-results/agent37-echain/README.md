# Cryptid D: quantified 3-adic E-chain and return-to-regular cylinders

**Status 2026-11-08:** source-connected, arbitrary-depth exact raw-machine identities, all Lean-audited in successful [manual original-source CI 42520521147](https://github.com/FlareZ123/bb6/actions/runs/42520521147) with the unmodified pinned original source and `#print axioms` checks. These results concern specified F/0 configurations and do not decide genuine blank-root nonhalting or BB(6). No claim of external novelty.

## Original six-state machine and notation

The exact D cryptid table is `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`. Write

`M(a,q,p;Y) = I_a((01)^q 0 1^p Y)`,

where `I_a` is F scanning a zero, blank left, followed by `a` ones. All finite right suffixes have implicit infinitely many blank zeros. The fixed marker `Y=01010111` is produced by the source-proved exceptional E,p=2 reset of Agent2.

## Arbitrary-depth original-machine E chain

[**EChainSource.lean**](EChainSource.lean) proves `BB6.Agent37EChain.chain_return`, for **every** depth `d`, `h>=1`, `q,p>=0`, and **arbitrary binary tail Y**:

```
M(1 + 4·3^d·h, q, 3d+p; Y)
   --[chainTime d h q raw original transitions]-->
M(1 + 4·8^d·h, q+2d, p; Y).
```

The exact time is recursively specified by `chainTime 0 h q=0` and

`chainTime (d+1) h q = 12K²+49K+58+6q + chainTime d (8h) (q+2)`,

where `K=4·3^d·h−1`. The proof inducts on `d` using Agent31's fully source-proved `e_packet`, with an elementary algebraic lemma guaranteeing `K>=0`. No machine simulation, arbitrary finite depth cap, or assumed first-return minimality is used.

## Universal A-exit resource theorem

[**EChainResidues.lean**](EChainResidues.lean) independently proves the exact residue arithmetic:

- At even E depth `d=2n`, taking `h=3s+2` gives `1+4·8^d·h=3ka+3` for some `ka>=0`.
- At odd E depth `d=2n+1`, taking `h=3s+1` gives the same A-congruence conclusion.

The same file encodes division-free reset-index sequences using `half9(0)=0`, `half9(n+1)=9·half9(n)+4`:

```
evenK(n,s) = 3·9^n·s + 5·half9(n) + 2
oddK(n,s)  = 9·9^n·s + 3·half9(n) + 1.
```

Their universally proven identities are

```
2·evenK(n,s)+1 = 3^(2n)   (6s+5)
2·oddK(n,s)+1  = 3^(2n+1) (6s+1).
```

[**EChainAExit.lean**](EChainAExit.lean) composes the source E chain with Agent2's original-machine exceptional reset `e_two_reset` and Agent35's universal `all_A_marker_returns`. Its `reset_even_depth` and `reset_odd_depth` theorems say:

**For every n,s,Q>=0 with `3d <= 2Q+6`, the original D machine starting from `M(3k+4,Q,2;01^6)` reaches, after some finite exact raw time, an F/0 section of one of the following three fully specified forms:**

```
I_N(1010111),   I_N(empty),   I_N(010101010),
```

with `d=2n, k=evenK(n,s)` or `d=2n+1, k=oddK(n,s)`. The existential raw time is constructed from the known exceptional reset duration, exact unbounded `chainTime`, and Agent35's original-source A completion.

The guard `3d <= 2Q+6` is exactly the sufficient unary-symbol budget for `d` E macro calls following the exceptional reset. In particular:

| Depth d | k family | Minimum Q |
| ---: | --- | ---: |
| 0 | 3s+2 | 0 |
| 1 | 9s+1 | 0 |
| 2 | 27s+22 | 0 |
| 3 | 81s+13 | 2 |
| 4 | 243s+202 | 3 |
| 5 | 729s+121 | 5 |

The independent fixed-depth [P2K13Source.lean](../agent37-p2-k13/P2K13Source.lean), originally source-checked in [CI 42519523558](https://github.com/FlareZ123/bb6/actions/runs/42519523558), supplies a concrete depth-three regression instance but is logically subsumed by the arbitrary-depth theorem.

## Complementary arbitrary-depth B-then-A exits

[**EChainBResidues.lean**](EChainBResidues.lean) and [**EChainBExit.lean**](EChainBExit.lean) resolve an additional source-valid branch at every positive depth. For a final E-chain index `a=1+4·8^d h` satisfying `a=3kb+2` and `8kb+10=3ka+3`, the source-certified `b_packet` moves the head from B to A, after which Agent35's universal A marker theorem returns to one of the three regular F/0 suffixes. The B call is valid because a positive E-chain depth provides `2d>=2` alternating pairs.

The congruence test is `a mod9=5`. The residue witnesses are exact and kernel-proved:

- **Even depth `d=2n>=2`:** `h=18s+1`, `k=9·9^n·s+half9(n)`.
- **Odd depth `d=2n+1`:** `h=18s+17`, `k=27·9^n·s+51·half9(n)+25`.

For **every** such n,s and initial Q satisfying `3d<=2Q+6`, original D source runs from `M(3k+4,Q,2;01^6)` to a regular F/0 section in finite exact primitive time. These source theorems include `k=27s+25` at depth one, `k=81s+4` at depth two, `k=243s+229` at depth three and infinitely deeper classes. The even depth zero exception is intentionally excluded because the guarded B macro requires an existing alternating pair.

**Original source CI [42521006551](https://github.com/FlareZ123/bb6/actions/runs/42521006551) passed**, with all new `#print axioms` audits restricted to Lean's standard logical axioms, no `sorryAx`.

## Implications and limits

The index condition is a 3-adic valuation classification of `2k+1`: `v₃(2k+1)=d` in these two families. For every depth there are infinitely many parameterized starts with a source-certified finite route back into the regular F/0 language. The proof does **not** show that all E resets satisfy one of those congruences, or that a specific genuine blank-root trajectory reaches the input. It gives no universal BB(6) upper bound and does not exclude all alternate exit configurations.

The complementary B-exit residue cylinders, E,p<=2 terminal resets with **changed** markers, and a truly blank-root-connected inductive invariant are major remaining directions. Avoid extrapolating conditional return grammar to global nonhalting.
