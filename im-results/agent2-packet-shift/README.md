# D Cryptid: complete original-source reentry for the safe packet residues

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
- Authentic blank-root Machine D exceptional returns are not yet covered by a global source-connected invariant. The current original-source twentieth return candidate is [`BlankTwentiethRejoin.lean`](../agent37-d-timing-cocycle/BlankTwentiethRejoin.lean). It uses one guarded E edge from `M(3k20+4,4,4;0 1^6)` to `L(8k20+9,8,5)`, with `k20=512*((u20-1)/3)+255`; `u20=3*((u20-1)/3)+1` by `t20%27=4`. This is **not source-certified**: run [42329147551](https://github.com/FlareZ123/bb6/actions/runs/42329147551) ended with its verification step cancelled after about 22 minutes; retry [42331004226](https://github.com/FlareZ123/bb6/actions/runs/42331004226) ended in failure after about 71 minutes while the verification step was still marked in progress. The GitHub Actions log endpoint returned HTTP 404 for the failed job, so no Lean diagnostic is available and no mathematical failure can be inferred. The workflow's declared timeout is 90 minutes. A small-base probe is being used to investigate whether `DRegular.run 2040` on the 116,920-bit seed is an avoidable computation bottleneck. Do **not** label twentieth true-blank reentry proved until full source chain succeeds without `sorryAx`.
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
