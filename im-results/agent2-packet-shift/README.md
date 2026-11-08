# D Cryptid: complete original-source reentry for the safe packet residues

## Added 8 November 2026: two arbitrary-depth exceptional marker languages

**Status:** Fully quantified *original six-state source theorems* compiled by Lean 4.36.0-rc2 from the unchanged archived machine sources, in [manual CI 42524657127](https://github.com/FlareZ123/bb6/actions/runs/42524657127). The workflow audits `#print axioms` and rejects `sorryAx` / native decide. These remain intermediate synthetic F/0 tape facts, with no claimed authentic blank-root reachability, Cryptid D halting decision, or exact BB(6).

Use `M(a,q,p;Y)=I_a((01)^q0 1^pY)`, regular `L(A,Q,B)=I_A((01)^Q1^B)` on the physical blank-extended tape, and marker families `Y_m=(01)^m11`, `Z_m=(01)^m0` for every natural `m`.

The strongest certified theorems in this extension are:

| Original-source theorem | Quantified statement | Source |
|---|---|---|
| `Agent2MarkerTower.all_p1_regular` | Every `M(a,q,p;Y_m)` with `a≥4,p≡1 (mod3)` returns physically to some regular `L`, for every marker depth `m` | [MarkerTowerSource.lean](./MarkerTowerSource.lean) |
| `Agent2MarkerTower.e_zero_drop` | `M(3k+4,q,0;Y_(m+1))` transitions **exactly** to `M(8k+5,0,2q+7;Y_m)` in `12k²+49k+50+4q` primitive steps | Same |
| `Agent2MarkerTower.e_zero_q0_regular` | Every `M(3k+4,3u,0;Y_(m+1))` reaches `L` | Same |
| `Agent2EAltTurn.turn_all` | The original A/0 scan `11(01)^(r+1)11` transforms into C/1 `(10)^(r+3)`, preserves *any* left tape `L` and any right suffix, in exactly `6r+20` steps | [EAltMarkerAll.lean](./EAltMarkerAll.lean) |
| `Agent2EAltTurn.full_E_many` | General original-machine E-return on `11(01)^(r+1)11` for all `k,q,r` and arbitrary suffix, exact time `12k²+49k+68+4q+6r` | Same |
| `Agent2MarkerZero.all_p1_regular` | Every `M(a,q,p;Z_m)` with `a≥4,p≡1 (mod3)` reaches `L`; redundant far-right zeros are treated by the proved original-machine physical-tape bisimulation | [MarkerZeroSource.lean](./MarkerZeroSource.lean) |
| `Agent2EAltPacketCompose.e_two_to_zero` | `M(3k+4,q,2;Y_(r+1))` transitions **exactly** to `M(8k+5,0,2q+6;Z_(r+2))`, in `12k²+49k+68+4q+6r` steps | [EAltPacketCompose.lean](./EAltPacketCompose.lean) |
| `Agent2EAltPacketCompose.e_two_q2_regular` | Every `M(3k+4,3u+2,2;Y_(r+1))` returns to the regular family for arbitrary `k,u,r` | Same |
| `Agent2EAltPacketCompose.e_two_k0_regular` | Every `M(3(3t)+4,q,2;Y_(r+1))` reenters regular L for **all** q, r and t via the original-source B terminal | Same |
| `Agent2MarkerZeroAZero.aZeroRegular` | Every zero-ended marker A terminal `M(3k+3,q,3r;Z_m)` has a finite regular reentry, for all k,q,r,m | [MarkerZeroAZero.lean](./MarkerZeroAZero.lean) |
| `Agent2EAltK2AZero.e_two_k2_q0_regular` | Every `M(3(3t+2)+4,3u,2;Y_(r+1))` returns to L after an E turn and an A p0 terminal, for all t,u,r | [EAltK2AZero.lean](./EAltK2AZero.lean) |

These are genuine independent whole-parameter symbolic source proofs. The proof connects: source `full_E_many` converts a positive-depth `Y` marker to a `Z` marker; when `q=3u+2`, the new unary-packet run `p=2q+6` has residue one, and the arbitrary-depth `Z` normalizer terminates in regular `L`. Both marker normalizers compose the already source-checked well-founded B/E packet `normalizeWithCount` with explicit A/B/E terminal source rules. The zero-ended A terminal consumes exactly the finite code `(10)^q(111)^r(10)^(m+1)` before the implicit blank.

**Verification:** source-normalized fixed marker `010111` is [CI 42521952399](https://github.com/FlareZ123/bb6/actions/runs/42521952399), all-depth `Y_m` is [CI 42522113484](https://github.com/FlareZ123/bb6/actions/runs/42522113484), arbitrary-left A-turn/E return is [CI 42523540597](https://github.com/FlareZ123/bb6/actions/runs/42523540597), all-depth `Z_m` is [CI 42524149772](https://github.com/FlareZ123/bb6/actions/runs/42524149772), composed E,p2,q2 is [CI 42524657127](https://github.com/FlareZ123/bb6/actions/runs/42524657127), k≡0(mod3) all-q closure is [CI 42524999965](https://github.com/FlareZ123/bb6/actions/runs/42524999965), and the all-depth A p0 plus k≡2(mod3),q≡0(mod3) extension is [CI 42525411105](https://github.com/FlareZ123/bb6/actions/runs/42525411105). The [manual workflow](../../.github/workflows/agent2-marker-two.yml) compiles source and ancestors. Fixed suffix proof [MarkerTwoSource.lean](./MarkerTwoSource.lean) is subsumed by the tower results. No need to reproduce its finite case separately.

**Open direction:** classify the remaining `Z_m` terminal exits with `p≡2(mod3)` and E with p≡0, then connect source-certified families to authentic blank-tape checkpoints. The E-turn produces `p=2q+6`. All q are closed when the initial E index k≡0(mod3); all k close when q≡2(mod3); and k≡2(mod3),q≡0(mod3) close by the new A p0 terminal. The residual positive-depth k≡1(mod3) branches and k≡2(mod3),q≡1(mod3) require further source reasoning. Neither absence of additional finite returns nor halt follows from the unclassified branches.

**Status: Lean source-certified all-parameter intermediate theorem (7 November 2026).**
Machine: `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---` (Cryptid D).
The exact BB(6) value and the authentic blank-tape nonhalting question are open.
This is a universal packet-family theorem from arbitrary F/0 starting configurations, with no claim that all configurations occur on the true blank orbit.

## Strongest theorem

Let
`M(a,q,p;Y) = I_a((01)^q 0 1^p Y)`, with `I_a(Z)` the physical original-machine F/0 section, unary prefix `1^a`, and right word `Z`. Fix `Y = 0 1^6`. Then for **every** `a,q,p∈ℕ` satisfying **`a≥4` and `p mod 3∈{0,1}`**, there exist natural numbers `T,A,Q,B` with the physical original machine satisfying

```text
run_original(T, M(a,q,p;0 1^6))  ≈  I_A((01)^Q 1^B).
```

The relation `≈` is physical tape equivalence `BoundaryPadding.ObsEq`, treating finitely appended blank zero cells as identical infinite blank-extended tapes. The time `T` is in **primitive original Turing-machine steps**, not an abstract macro count. The quantified `T` can be constructed by a well-founded packet recursion and a final original-source boundary macro. Nothing asserts universal closure of future returns from this endpoint.

**Formal statement:** [`PacketSafeReentry.lean`](./PacketSafeReentry.lean), theorem `BB6.Agent2PacketSafeReentry.all_safe_packets_regular`. The original-source Lean verification [run 42331774454](https://github.com/FlareZ123/bb6/actions/runs/42331774454) at SHA `1f842379f9b241b794e9f28ea4a3e25ce0dc14d1` **succeeded**, printing only `[propext, Quot.sound]` for the closing theorem, without `sorryAx`, native-decide, or extra axioms. This preserves the original source definition and state-6 halt semantics; the script restores archived original Lean sources before compilation.

## Proof architecture and exact terminal classification

1. [`PacketSafeExit.lean`](./PacketSafeExit.lean) extends the existing well-founded `PacketRank.lean`. Each guarded B/E packet step reduces `q+p` by one, preserves `p mod3`, and preserves `a≥4`. Hence normalization is finite, and for safe residue `p%3≠2` its final shape must be an A section, B with `q=0`, or E with `p=0/1`. This last shape assertion is purely combinatorial and excludes the exceptional E,p=2 reset. CI [42329978448](https://github.com/FlareZ123/bb6/actions/runs/42329978448) passed.
2. [`PacketNormalizeSource.lean`](./PacketNormalizeSource.lean) bridges **every** rank-guarded abstract transition to a source-proved `PacketPaths.Edge`, then to an actual original six-state `run` through `PacketPaths.path_sound`, for **arbitrary** finite physical tail `Y`. This is the universal source bridge `normalized_original_source`, with a guarded phase of at most `q+p` macro returns. CI [42330214064](https://github.com/FlareZ123/bb6/actions/runs/42330214064) passed.
3. For the final fixed-tail packet, the full **original-source** boundary table is:
   - A with `a=3k+3, p=3r`: [`PacketZeroBoundarySource.a_zero_boundary`](./PacketZeroBoundarySource.lean) reaches pure unary `I_(8k+17+2q+8r)`. Source is the general `Agent35.full_A_code` with q `10` tokens and r `111` tokens, followed by a zero and six ones.
   - A with `a=3k+3, p=3r+1`: [`AOnePacketBoundarySource.a_p1_boundary`](./AOnePacketBoundarySource.lean) reaches pure unary `I_(8k+29+2q+8r)`, using the same original general A-code plus one physically implicit terminal blank.
   - B with `a=3k+2,q=0`: [`BoundaryBZero.b_zero_source`](./BoundaryBZero.lean) reaches `I_(8k+9+p)(0 1^6)`, the regular form `L(8k+9+p,1,5)`.
   - E with `a=3k+4,p=0`: [`PacketZeroBoundarySource.e_zero_boundary`](./PacketZeroBoundarySource.lean) reaches `I_(8k+5)(0 1^(2q+12))`, the regular form `L(8k+5,1,2q+11)`.
   - E with `a=3k+4,p=1`: [`BoundaryBZero.e_one_regular`](./BoundaryBZero.lean) is **already** regular `L(a,q+2,5)`, so this boundary costs zero additional primitive steps.
4. [`PacketOneReentry.lean`](./PacketOneReentry.lean) first composes all p=1 mod3 cases (original-source CI [42331226932](https://github.com/FlareZ123/bb6/actions/runs/42331226932)). [`PacketSafeReentry.lean`](./PacketSafeReentry.lean) closes the p=0 mod3 half and disjoins them. All source macro imports are the original archived Lean definitions. The final theorem's proof includes the exact `BoundaryPadding.source_chain` compositional physical-tape argument.

The *source-return* formulas here are specializations of Agent31's 3 November [packet-descent mathematical table](../agent31-d-exceptional/packet-descent.md). The new contribution is the **single quantified, original-source-certified, all-guarded-depth composition**: the earlier abstract rank and boundary formulas did not form one original-machine L reentry certificate. This is a reusable unbounded closure theorem for a selected packet family, with clear outstanding assumptions.

## New source-certified first exceptional p=2 return and k≡0 closing branch

The [`PacketP2ResetSource.lean`](./PacketP2ResetSource.lean) extension is **original-source-certified** at successful [CI 42332391372](https://github.com/FlareZ123/bb6/actions/runs/42332391372), SHA `f7b8144ee54b2f2e138cf99007aecad5611027ba`, with `[propext, Quot.sound]` and no `sorryAx`. It uses Agent37's unchanged source-proved `E110111Pairs.full_E_110111_pairs_raw` and a literal tape-word identity, and derives, for every k,q:

```text
run_original(12k²+49k+68+4q, M(3k+4,q,2;0 1^6))
    = M(8k+5,0,2q+6;(01)^3 11).
```

The new marker is precisely `01010111`. This equality holds for arbitrary k,q and specifies exactly where the original safe-tail grammar stops being directly applicable. In the **infinite subfamily k=3t**, the reset output is a B with q=0, and the second certified source return gives the exact regular section

```text
run_original(
   (12(3t)² + 49(3t) + 68 + 4q)
   + (12(8t+1)² + 49(8t+1) + 40),
   M(9t+4,q,2;0 1^6)
) = L(64t+2q+23,3,2).
```

Formal theorems: `e_two_reset`, `b_zero_any`, and `e_two_k0_regular`. The source-certified p=2 exception is therefore **partially closed**, leaving at least k≡1,2 and the more general changed-tail recurrences. The claim is only an infinite *input-packet family*, not a statement about whether those inputs occur on the authentic blank orbit.

## Exact residual and relevance to the true blank root

- For `p≡2 (mod3)`, rank normalization still terminates. It may exit through A, B with `q=0`, or E with `p=2`. The latter is source-normalized to a changed marker `01010111`. The fixed-tail E,p=2 reset family is now source-composed to regular L for all q in `k≡0 (mod3)`, `k≡2 (mod3)`, and `k≡1 (mod9)`, covering seven of nine k residue classes modulo nine. The remaining `k≡4,7 (mod9)` changed-tail dynamics and the authentic blank-root connection remain open.
- Authentic blank-root Machine D exceptional returns are not yet covered by a global source-connected invariant. The current original-source twentieth return candidate is [`BlankTwentiethRejoin.lean`](../agent37-d-timing-cocycle/BlankTwentiethRejoin.lean). It uses one guarded E edge from `M(3k20+4,4,4;0 1^6)` to `L(8k20+9,8,5)`, with `k20=512*((u20-1)/3)+255`; `u20=3*((u20-1)/3)+1` by `t20%27=4`. This is **not source-certified**: run [42329147551](https://github.com/FlareZ123/bb6/actions/runs/42329147551) ended with its verification step cancelled after about 22 minutes; retry [42331004226](https://github.com/FlareZ123/bb6/actions/runs/42331004226) ended in failure after about 71 minutes while the verification step was still marked in progress. A later retry [42359852323](https://github.com/FlareZ123/bb6/actions/runs/42359852323) again ended with the verification step marked cancelled after about 23 minutes, despite no newer run of the same workflow appearing in the run list. The GitHub Actions log endpoint returned HTTP 404 for the earlier failed job; no Lean diagnostic is available for these cancellations, so no mathematical failure can be inferred. The workflow's declared timeout is 90 minutes. Manual probe [42359725968](https://github.com/FlareZ123/bb6/actions/runs/42359725968) evaluated `DRegular.run 2040` from `(a,q,b)=(2,0,0)` and returned `(q,b)=(0,0)`. This only rules out a naive substitution of base `a=2`: `DRegularShift.run_shift` preserves the endpoint control state only when the actual seed agrees modulo `3^2040`. The required residue of the 116,920-bit twentieth seed has not been computed, so the probe does not diagnose the root-chain bottleneck. Do **not** label twentieth true-blank reentry proved until full source chain succeeds without `sorryAx`.
- Independent exact DRegular arithmetic predicts twenty-first and twenty-second exception inputs after the twentieth candidate. A twenty-second off-L endpoint is `M(512u+434,1,13;0 1^6)`, with `p=13≡1 (mod3)`, now covered by the **unconditional synthetic source** theorem. Connecting these later endpoints to the authentic blank trajectory requires the original-source root-chain proof, and further future exceptions may still enter p=2 cases.
- **Next discriminating test:** prove either a source-backed finite-tail invariant routing every *authentic* p=2 reset back to a safe packet or L, or exhibit a literal original-machine fatal event from that reachable family. A bounded search or an arithmetic DRegular lookahead alone is not enough to decide Cryptid D.

## Reproduction

Manual, source-pinned workflow `.github/workflows/agent2-a-one-packet-boundary.yml` reconstructs original source files with `im-results/agent31-cryptid-boundary/unpack.py` and `im-results/agent25-cryptid-doublezero/unpack.py`, compiles the exact upstream `Boundary`, `TokenCode`, `ABridgeCode`, `CryptidPairs`, `CryptidTriplePairs`, `PacketSource`, `PacketRank`, and `PacketPaths` modules, and then checks the four new Agent2 proof files with Lean 4.36.0-rc2. The workflow fails on `sorryAx` or native-decide dependence in the concluding axiom output and has no per-commit trigger. Preserve source hashes and the exact full CI run ID for any public assertion. 


## Source-composed seven-of-nine exceptional E,p=2 coverage (7 November 2026)

Agent31's previously stub-checked compositions are now verified against the unchanged original D source in [manual CI 42359163994](https://github.com/FlareZ123/bb6/actions/runs/42359163994), commit `aeec0ba7cb2b254495feed1cbf72a1cc3da718f5`, Lean 4.36.0-rc2. The workflow extends the existing manual source audit and compiles both `P2K2Source.lean` and `P2K1Mod9Source.lean` after the exact source dependencies. Their six quantified endpoint theorems each print only `[propext, Quot.sound]`; the workflow rejects `sorryAx` and `_native.native_decide`.

Combined with `e_two_k0_regular` in this directory:

- `k≡0 (mod 3)`: all q reenter regular L after the E,p=2 reset and a B,q=0 return.
- `k≡2 (mod 3)`: all q reenter regular L after the E,p=2 reset and an A-code return, with three q-mod-3 endpoint forms.
- `k≡1 (mod 9)`: all q reenter regular L after the E,p=2 reset, a second E return, and an A-code return, with three q-mod-3 endpoint forms.

These disjoint families cover seven of nine k residue classes modulo nine. The remaining classes are `k≡4,7 (mod 9)`. The source theorems prove designated exact `run` endpoints for all natural parameters; they do not assert that those endpoints are the first physical F/0 visits. The independent Python regressions establish first-return behavior only on their finite test ranges. None of these synthetic F/0 packet results establishes reachability from the authentic blank tape or decides BB(6).
