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

## q=4 exceptional E/E source-section return (actual-source CI pending)

A stronger composition candidate is in [EERootBEA.lean](EERootBEA.lean), theorem `q4_exceptional_EE_BEA_section`. For every `m ≥ 0`, put
`u=2187*m+1647=27*(81*m+61)`. Starting from Agent 2's `sourceStart(u,4)`, the first exceptional E/E macro reaches `M(192u+161,2,5;01^6)`. The explicit source path then has two B edges, one E edge, the existing E,p=2 reset, and the new B->E->A corridor, ending in a physical `regularSection` up to `ObsEq`.

The parameters are
```text
z  = 81*m+61
k0 = 1728*z+53
k1 = 4608*z+144
k2 = 12288*z+386
k3 = 32768*z+1031
h  = 1769472*m+1333253
t  = 2097152*m+1580151
```
They satisfy `192u+161=3*k0+2`, `8*k0+10=3*k1+2`, `8*k1+10=3*k2+4`, `8*k2+9=3*k3+4`, `8*k3+5=1+12*h`, and `1+32*h=27*t+20`. The E2 reset leaves resource 10, exactly enough for the d=1 B->E->A corridor.

**Evidence status:** the arithmetic and source-chain composition type-check in a local Lean harness with stubbed upstream declarations; that checks the composition interface, not the real machine source. The actual-source audit is configured in `.github/workflows/agent37-p2-k13.yml` but has not yet been dispatched. Do not cite this theorem as source-certified until that full workflow passes.

**Scope limitation:** `sourceStart(u,4)` is an Agent 2 DRegular source section, not a proved blank-tape-root state. The missing fact is whether the blank-root prefix chain reaches `L(59049*m+44494,4,1)` for any `m). Agent 2 has been asked to identify or prove that prefix before this cylinder is treated as blank-root progress.

## New B-to-E-to-A corridor (Lean source composition verified)

The B-exit partition has a third branch beyond B-to-A and B-to-B-to-A: after the E-chain, a B packet can move to E, then one more E packet can move directly to A. This is composed in [EChainBEExit.lean](EChainBEExit.lean). The focused manual source-audit workflow passed on 2026-11-12 (run 43273085496); all five new declarations have only standard `propext` and `Quot.sound` dependencies, with no `sorryAx` or native-decision axiom.

For every \(d,h,t,q,p\in\mathbb N\) with \(h\ge1\), \(d\ge1\), and
\[
1+4\cdot8^d h=27t+20,
\]
the proposed theorem chain_B_E_A source-composes:

\`\`\`text
M(1+4·3^d·h, q, 3d+3+p; Y_3)
  -- d E edges --> M(27t+20, q+2d, 3+p; Y_3)
  -- B edge --> M(72t+58, q+2d-1, 3+p; Y_3)
  -- E edge --> M(192t+153, q+2d+1, p; Y_3).
\`\`\`

The final unary index is \(192t+153=3(64t+51)\), so Agent35's all-depth A-marker return closes it. Composing the initial exceptional reset gives reset_B_E_A: for \(2k+1=3^d h\) and \(3d+3\le2Q+6\), the fixed-tail input \(M(3k+4,Q,2;01^6)\) reaches one of the three established regular endpoints whenever \(1+4\cdot8^d h\equiv20\pmod{27}\).

This is an explicit infinite residue cylinder. Since \(8^6\equiv1\pmod{27}\), the congruence is equivalent to the following \(h\pmod{27}\) classes, indexed by \(d\pmod6\):

| \(d\bmod6\) | \(h\bmod27\) | odd \(h\bmod54\) (as required by \(2k+1=3^d h\)) |
|---:|---:|---:|
| 0 | 25 | 25 |
| 1 | 20 | 47 |
| 2 | 16 | 43 |
| 3 | 2 | 29 |
| 4 | 7 | 7 |
| 5 | 11 | 11 |

The source-level composition is deliberately separated from the modular parameterization. The first audit attempt stopped before reaching this file because the pre-existing EChainDoubleBExit.lean draft fails in b_twice and reset_double_B_to_A and reports `sorryAx`. That draft is excluded from the focused workflow; its double-B claims remain unverified and must not be used as evidence. The successful run compiled EChainBEExit.lean after EChainBExit.lean and passed the forbidden-axiom check. This corridor does not cover the other B-to-E residue classes or establish authentic blank-root reachability.

## Implications and limits

The index condition is a 3-adic valuation classification of `2k+1`: `v₃(2k+1)=d` in these two families. For every depth there are infinitely many parameterized starts with a source-certified finite route back into the regular F/0 language. The proof does **not** show that all E resets satisfy one of those congruences, or that a specific genuine blank-root trajectory reaches the input. It gives no universal BB(6) upper bound and does not exclude all alternate exit configurations.

The complementary B-exit residue cylinders, E,p<=2 terminal resets with **changed** markers, and a truly blank-root-connected inductive invariant are major remaining directions. Avoid extrapolating conditional return grammar to global nonhalting.
