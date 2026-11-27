# Cryptid D: arbitrary-depth E-chain and regular-return cylinders

## Current mathematical status

This dossier contains several **original-source-certified conditional return theorems** for the six-state D machine. They prove finite exact raw-machine routes from specified F/0 packet sections back into the regular F/0 language. They do **not** prove that a genuine blank-tape orbit reaches every stated input, decide all D trajectories, or establish a BB(6) upper bound.

The strongest established results are:

1. An arbitrary-depth E-chain for every finite binary tail.
2. Even- and odd-depth residue families whose E-chain endpoint takes an A exit.
3. Complementary positive-depth B-to-A residue families.
4. A third B-to-E-to-A exit cylinder, including a physical `ObsEq` bridge into Agent 2's `regularSection` language.

A further q=4 E/E composition is recorded below as a **candidate source-section closure**. Its arithmetic and composition shape have been locally type-checked against stubbed upstream declarations, but its full actual-source Lean audit has not yet run. Its start is a DRegular source section, not a proved blank-root state.

## Machine semantics and notation

The original six-state table is

`1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`.

Write

`M(a,q,p;Y) = I_a((01)^q 0 1^p Y)`,

where `I_a` is F scanning a zero, with blank left tape and `a` leading ones on the right. A finite right suffix is followed by infinitely many blank zeros. The fixed marker `Y3=01010111` is produced by Agent 2's source-proved exceptional E,p=2 reset. The fixed-tail packet `01^6` means one zero followed by six ones, again with an infinite blank continuation.

`ObsEq` is the repository's physical far-blank observational equivalence. It is not raw finite-list equality: in particular, one of the regular endpoints below differs from its `regularSection` representation by one explicit trailing blank zero.

## All-stack guarded E-two packet return (27 November 2026)

The exact original six-state source now admits an **all-`k,q`** transition
for the short E-two frontier `0100Y`. Write `M(a,q,p;Y)` as above.
[**E2ShortAll.lean**](E2ShortAll.lean) proves both branches of the single
case split with no arbitrary finite upper bound and arbitrary binary `Y`:

- **Zero alternating pairs:** `M(3k+4,0,2;0100Y) → M(8k+3,0,4;010101011Y)`,
  in exactly `12k²+49k+100` primitive steps. This route uses the B-state sweep.
- **Positive alternating pairs (`q≥1`):**
  `M(3k+4,q,2;0100Y) → M(8k+5,0,2q+2;01⁸Y)`,
  in exactly `12k²+49k+64+4q` primitive steps. The source proof
  uses an unbounded D-state pair sweep, not numerical sampling.

The `short_all_implicit_blank` theorem furthermore proves the **physical
infinite-tape** result when the only explicit tail bits are `01`:
the machine's implicit zeros supply the two guard zeros. This is
`BB6.BoundaryPadding.ObsEq`, not literal equality of finite lists.
The individual source proofs are
[PacketEZeroAnyTail.lean](PacketEZeroAnyTail.lean),
[E2ShortQ3.lean](E2ShortQ3.lean),
[E2ShortPositive.lean](E2ShortPositive.lean),
[E2ShortPhysical.lean](E2ShortPhysical.lean) and
[E2ShortZero.lean](E2ShortZero.lean). The same work also certifies, for
all `k,q,Y`, the E-zero packet transition
`M(3k+4,q,0;01Y) → M(8k+5,0,2q+7;Y)` at
`12k²+49k+50+4q` primitive steps.

**Source status:** both branches, their single all-q wrapper, and the
unpadded physical theorem passed original-machine Lean 4.36.0-rc2
[CI 46081744437](https://github.com/FlareZ123/bb6/actions/runs/46081744437),
with standard axioms `propext` and `Quot.sound`; no `sorryAx` or
native decision axiom. These are conditional prepared-tape transitions.
They do not establish authenticity of a blank-root visit or a new
BB(6) bound. They compress the exceptional E-zero and E-two cases in
the [107-call packet reconstruction](Astep2PacketTransducer.md).

## Two independent alternating stacks and complementary 0011 guard (27 November 2026)

The local source machine admits a universal A/0 turn for every `r≥0`,
arbitrary left tape `L`, and arbitrary right tail `Y`:
`11(01)^r00Y → D/1, 1^(2r+4)Y` in exactly `4r+12`
primitive transitions, leaving `L` intact
([E2AlternatingTurn.lean](E2AlternatingTurn.lean)). Combining this
with unbounded D and B sweeps and the exact E source prefix yields
the **two-stack** laws, for arbitrary `k≥0, r≥1, q≥1, Y`:

- `M(3k+4,q,2;(01)^r00Y) → M(8k+5,0,2q+2;0 1^(2r+6)Y)`,
  at `12k²+49k+60+4q+4r` primitive steps.
- At `q=0`: `M(3k+4,0,2;(01)^r00Y) → M(8k+3,0,4;010101011 1^(2r−2)Y)`,
  at `12k²+49k+96+4r` steps.

Both are proved with all parameters, not extrapolated from samples, in
[E2AlternatingPacket.lean](E2AlternatingPacket.lean), checked against
the **literal original six-state machine** in
[CI 46082265496](https://github.com/FlareZ123/bb6/actions/runs/46082265496).
[E2AlternatingAll.lean](E2AlternatingAll.lean) unifies the two cases for
all `k,q,r≥0` (its input has `(01)^(r+1)00Y`), and proves the
observational version with an **implicit** far-right `00` after the
entire `(01)^(r+1)` suffix, verified in
[CI 46082491713](https://github.com/FlareZ123/bb6/actions/runs/46082491713).

A separate local `r=0` corridor, when the right tail begins `0011Y`,
takes **four fewer steps** to the same respective endpoints as the
`0100Y` rule in the previous section:
`M(3k+4,q,2;0011Y) → M(8k+5,0,2q+2;01^8Y)`,
for `q≥1` at `12k²+49k+60+4q` steps, and for `q=0` reaches
`M(8k+3,0,4;010101011Y)` at `12k²+49k+96` steps.
See [E2DoubleZeroGuard.lean](E2DoubleZeroGuard.lean),
[CI 46082697518](https://github.com/FlareZ123/bb6/actions/runs/46082697518).

All these results are **prepared source-section theorems**. They make
no new assertion about any genuine blank-root reachability or the
total BB(6) function. Keep the independent physical blank-equivalence
boundary explicit when composing theorems.

## Arbitrary-depth original-source E-chain

[**EChainSource.lean**](EChainSource.lean) proves `BB6.Agent37EChain.chain_return` for every depth `d), `h≥1), `q,p≥0), and arbitrary binary tail `Y`:

```text
M(1 + 4·3^d·h, q, 3d+p; Y)
   -- exact original E transitions -->
M(1 + 4·8^d·h, q+2d, p; Y).
```

The exact time is recursively specified by

```text
chainTime 0 h q = 0
chainTime (d+1) h q =
  12K² + 49K + 58 + 6q + chainTime d (8h) (q+2),
  K = 4·3^d·h - 1.
```

The proof inducts on `d` using Agent 31's fully source-proved `e_packet`. It has no finite depth cap, no machine simulation, and no assumed first-return minimality.

## E-chain A exits and resource bounds

[**EChainResidues.lean**](EChainResidues.lean) proves the exact residue arithmetic. At even depth `d=2n), taking `h=3s+2` gives an A-congruent endpoint. At odd depth `d=2n+1`, taking `h=3s+1` does the same. The division-free reset-index sequences are

```text
half9(0)=0,  half9(n+1)=9·half9(n)+4

evenK(n,s) = 3·9^n·s + 5·half9(n) + 2
oddK(n,s)  = 9·9^n·s + 3·half9(n) + 1.
```

Their kernel-proved identities are

```text
2·evenK(n,s)+1 = 3^(2n)   (6s+5)
2·oddK(n,s)+1  = 3^(2n+1) (6s+1).
```

[**EChainAExit.lean**](EChainAExit.lean) composes the arbitrary-depth source E-chain with Agent 2's original-source exceptional reset `e_two_reset` and Agent 35's universal `all_A_marker_returns`. For `d=2n) or `d=2n+1`, with the corresponding `k=evenK(n,s)` or `oddK(n,s)`, and resource guard

`3d ≤ 2Q+6`,

the fixed-tail input `M(3k+4,Q,2;01^6)` reaches one of these three regular F/0 forms in finite exact raw time:

```text
I_N(1010111),   I_N(empty),   I_N(010101010).
```

The guard is the sufficient unary-symbol budget for the `d` E macro calls after the exceptional reset. The independent fixed-depth [P2K13Source.lean](../agent37-p2-k13/P2K13Source.lean), source-checked in [CI 42519523558](https://github.com/FlareZ123/bb6/actions/runs/42519523558), is a depth-three regression instance and is logically subsumed by the arbitrary-depth result.

## Complementary B-to-A exits

[**EChainBResidues.lean**](EChainBResidues.lean) and [**EChainBExit.lean**](EChainBExit.lean) prove another original-source branch at every positive depth. When the final E-chain index `a=1+4·8^d h` satisfies `a mod 9=5), the source-proved `b_packet` takes B directly to A, after which Agent 35's universal A-marker theorem returns to a regular F/0 section.

The residue witnesses are:

- **Even depth `d=2n≥2`:** `h=18s+1`, `k=9·9^n·s+half9(n)`.
- **Odd depth `d=2n+1`:** `h=18s+17`, `k=27·9^n·s+51·half9(n)+25`.

For every such `n,s) and initial `Q` satisfying `3d≤2Q+6`, the fixed-tail input `M(3k+4,Q,2;01^6)` reaches a regular F/0 section in finite exact primitive time. The depth-zero exception is intentionally excluded because the guarded B macro requires an existing alternating pair.

The original-source audit passed [CI 42521006551](https://github.com/FlareZ123/bb6/actions/runs/42521006551), with no `sorryAx`.

## B-to-E-to-A exit cylinder

[**EChainBEExit.lean**](EChainBEExit.lean) proves a third branch beyond B-to-A and B-to-B-to-A. If

```text
1 + 4·8^d·h = 27t+20,   h≥1,   d≥1,
```

then the E-chain endpoint takes one B edge to index `72t+58`, one E edge to index `192t+153), and then Agent 35's all-depth A-marker completion returns to one of the three regular F/0 endpoint shapes:

```text
M(1+4·3^d·h, q, 3d+3+p; Y3)
  -- d E edges --> M(27t+20, q+2d, 3+p; Y3)
  -- B -->         M(72t+58, q+2d-1, 3+p; Y3)
  -- E -->         M(192t+153, q+2d+1, p; Y3).
```

The last index is `192t+153=3(64t+51)`. Composing the exceptional reset gives `reset_B_E_A`: whenever `2k+1=3^d h`, `3d+3≤2Q+6`, and `1+4·8^d h≡20 (mod 27)`, the fixed-tail input `M(3k+4,Q,2;01^6)` reaches one of the three regular endpoints.

The congruence is an explicit infinite cylinder. Since `8^6≡1 (mod 27)`, the odd `h) classes required by `2k+1=3^d h` are:

| `d mod 6` | `h mod 27` | odd `h mod 54` |
|---:|---:|---:|
| 0 | 25 | 25 |
| 1 | 20 | 47 |
| 2 | 16 | 43 |
| 3 | 2 | 29 |
| 4 | 7 | 7 |
| 5 | 11 | 11 |

### Physical regularSection bridge

The same file proves `regularEndpoint_reentry`, converting all three endpoint shapes into Agent 2's physical `regularSection` language:

- first endpoint: `regularSection (n+1) 2 2`, exactly;
- second endpoint: `regularSection n 0 0`, exactly;
- third endpoint: `regularSection n 4 0` up to one explicit trailing blank zero, handled by `BB6.Padding.tapeEq_pad`.

The wrappers `chain_B_E_A_reentry`, `reset_B_E_A_reentry`, and `source_chain_B_E_A_reentry` expose this bridge. The source-chain wrapper requires an already-proved `ObsEq` prefix to the canonical marker; it does not establish that a blank-root orbit reaches that marker.

**Verification:** the base B->E->A source audit passed [CI 43273085496](https://github.com/FlareZ123/bb6/actions/runs/43273085496). The physical `regularSection` bridge passed [CI 43275543784](https://github.com/FlareZ123/bb6/actions/runs/43275543784). The audited declarations have only standard `propext` and `Quot.sound` dependencies; no `sorryAx` or native-decision axiom was reported.

The first double-B draft attempted to carry `p+3` and `p+6` through B edges. That suffix accounting was incorrect: the exact original-source theorem `Agent31PacketSource.b_packet` is `M(3k+2,q+1,p;Y) → M(8k+10,q,p;Y)`, so a B edge preserves `p`. The corrected `EChainDoubleBExit.lean` now composes two B edges with `p` unchanged and sends the resulting packet to Agent 35's all-parameter A-marker closure with the same `p`. On the residue cylinder `1+4·8^d·h = 27t+17`, the arbitrary-depth E prefix supplies `q+2d≥2` (since `d≥1`), so both B edges are enabled. The corrected source composition is submitted for manual original-source audit; the previous `p+3/p+6` version and its downstream numerical endpoint are withdrawn.

A concrete nonempty instance is `concrete_reset_double_B_to_A`: `k=61`, `Q=0`, `d=1`, `h=41`, `t=48`. The reset input is `M(187,0,2;01^6)`, the P2 reset produces `M(493,0,6;01010111)`, one E-chain step gives `M(1313,2,3;01010111)`, and the two B edges give `M(9354,0,3;01010111)`. The A-marker closure therefore starts at A-index `3117` with suffix budget `p=3, quotient `r=1, and reaches `L(24956,2,2)`. This is a prepared-packet witness, not a blank-root reachability claim.

The concrete source wrapper was repaired in commit `9918fe91715c86650d80d6042d3cee6a245a84a0`: the two B edges preserve `p=3`, so the B endpoint, A input, and composed source chain all use `packet 9354 0 3 marker`; the A macro and its `close_zero` theorem both use quotient `r=1` (`aTime0 3117 0 1`), and `endpointZero 24955` converts to `L(24956,2,2)`. The earlier p=9/r=3 terms were inconsistent and have been removed. This source correction is **not yet locally preflighted or CI-audited**; the manual `agent37-p2-k13.yml` workflow must be rerun against the corrected file.

The separate `DRegularFirstExit.seed24972` experiment starts from `L(24972,2,2)`, not from this concrete reset endpoint. Its 5,648-step q=4 E/A model certificate is not a continuation of the `L(24956,2,2)` source route and must not be used to claim a second return from the concrete reset.

For the actual `L(24956,2,2)` endpoint, Agent 2 has prepared an uncompiled candidate in [`Seed24956SecondReentry.lean`](../agent2-root-language-exit/Seed24956SecondReentry.lean). An independent simulation of the DRootL arithmetic step table reaches after 86 transitions `L(107283033157493534200791430928221345342090,5,1)`, with `a≡23638 (mod 59049)` and `a≡4 (mod 9)`. This is an E exit of the form `L(3k+4,5,1)`, where `k=35761011052497844733597143642740448447362`; the submitted `ExceptionalESafeCanonical.all_E_safe_reentry_canonical` theorem covers q=5. The candidate attempts to lift the 86-step run through `DRegularSourceShift.lifted_original_run` and compose the safe-E closure with this concrete reset. It remains **uncompiled** and is not yet an original-source-certified second return.

## q=4 exceptional E/E source-section composition candidate

[**EERootBEA.lean**](EERootBEA.lean) contains theorem `q4_exceptional_EE_BEA_section`. For every `m≥0), set

```text
u  = 2187m+1647 = 27(81m+61)
z  = 81m+61
k0 = 1728z+53
k1 = 4608z+144
k2 = 12288z+386
k3 = 32768z+1031
h  = 1769472m+1333253
t  = 2097152m+1580151.
```

The starting configuration is Agent 2's `sourceStart(u,4)`, namely the DRegular source section

`L(27u+25,4,1) = L(59049m+44494,4,1)`.

The existing E/E source theorem reaches `M(192u+161,2,5;01^6)`. The proposed exact continuation is

```text
M(192u+161,2,5;01^6)
  -- B(k0) --> M(3k1+2,1,5;01^6)
  -- B(k1) --> M(3k2+4,0,5;01^6)
  -- E(k2) --> M(3k3+4,2,2;01^6)
  -- E,p=2 reset --> M(8k3+5,0,10;Y3)
  -- B->E->A --> regularSection.
```

The arithmetic identities are

```text
192u+161 = 3k0+2
8k0+10  = 3k1+2
8k1+10  = 3k2+4
8k2+9   = 3k3+4
8k3+5   = 1+12h
1+32h   = 27t+20.
```

Thus the E,p=2 reset leaves resource 10, exactly the `3d+3+p` budget for the verified B->E->A corridor at `d=1,p=4`.

**Evidence status (original-source CI passed):** the corrected full audit [CI 43312703231](https://github.com/FlareZ123/bb6/actions/runs/43312703231) succeeded on 2026-11-12 with Lean 4.36.0-rc2, compiling the pinned original machine sources, `ExceptionalE7SecondSafe.lean`, `EChainBEExit.lean`, and `EERootBEA.lean`. The final axiom audit for `q4_exceptional_EE_BEA_section` is exactly `[propext, Quot.sound]`; the workflow's `sorryAx` / native-decision rejection passed. The earlier failure [CI 43275820208](https://github.com/FlareZ123/bb6/actions/runs/43275820208) was repaired by importing the B-general dependency and splitting the `q-1) predecessor case before the replicate rewrite, then normalizing append associativity. This certifies the stated original-source composition from every specified DRegular source section to a physical `regularSection`; it does not certify that any such start occurs on the authentic blank-root orbit.

### Quantitative q=4 endpoint floor (original-source Lean verified)

The new module EERootBEAFloor.lean proves
**BB6.Agent37EERootBEAFloor.q4_exceptional_EE_BEA_section_affine_floor**:
for every m, the source run from sourceStart (2187*m+1647) 4 reaches
a physical regularSection a q b with

**1,073,741,824*m + 809,037,723 ≤ a**.

The bound is exact from the carried A-marker floor
n ≥ 8*(64*t+50)+11 = 512*t+411, with
t=2,097,152*m+1,580,151; the physical-section conversion gives a=n
or a=n+1. The simpler uniform a≥411 theorem is retained as a
corollary. Original-source CI run 43410773388 passed, and both floor
theorems have axiom dependencies [propext, Quot.sound] with the
sorryAx / _native.native_decide gate passing.

This is still only a conditional source-section return: it does not show
that the authentic blank-root orbit reaches the q=4 cylinder.

**Blank-root boundary:** this is a DRegular source-section theorem, not a blank-tape-root theorem. Its starting index is `L(9t+7,4,1)` with `t=6561m+4943≡2 (mod 27)`. The currently documented blank-root chain rows of the form `L(9t+7,q,1)` have `(q,t mod 27)=(7,6),(5,4),(8,14),(6,17),(9,8)); none is the q=4 cylinder. This is only a comparison with the currently documented rows, not an unreachability proof. The exact missing obligation is a blank-root prefix to any `L(9t+7,4,1)` with `t≡2 (mod 27)), or a proof that no such prefix occurs. Agent 2 and Agent 36 have been asked to identify this prefix. Do not widen the residue search or describe this candidate as blank-root progress before that connection is established.


## External A_step2 halting-cylinder replay and packet exit

The intermediate replay in [Astep2BoundaryReplay.mjs](Astep2BoundaryReplay.mjs), documented in [Astep2BoundaryReplay.md](Astep2BoundaryReplay.md), reproduces the pinned external proof's 107 A_step2 calls, branch word, eleven unary/suffix checkpoints, and all finite-tail alternating-block checks. It is a computational cross-check, not a new Lean proof.

The first ten outputs lie in the regular \((01)^q1^b\) language and end at the exceptional E, \((q,b)=(4,1)\) exit. [Astep2PacketExitTrace.md](Astep2PacketExitTrace.md) records the initial packet boundary. The canonical all-call packet transducer is in [Astep2PacketTransducer.md](Astep2PacketTransducer.md): call 11 yields \(P(0,8;F_7)\); calls 12–17 follow PacketRank B/E updates and the P2 reset; calls 18–23 follow the E-chain marker \(Y_3=01010111\); call 24 is the canonical E-zero map \(P(1,0;Y_3)\to P(0,9;U_6)\), with \(U_6=010111\).

The updated replay script checks all 107 canonical packet states, seven E-zero transitions, five E-two reset cases, and the terminal packet \(P(1,2;011)\). The first P2 reset has \(k\equiv169\pmod{243}\), outside the currently encoded EChain B/E/A corridors. The next formalization targets are the general E-zero source lemma and an E-two reset theorem parameterized by \((q,Y)\).

This work does not establish a blank-root prefix to the external halting cylinder, a universal BB(6) upper bound, or the exact value of BB(6).

## Remaining obligations

- Establish the missing blank-root prefix to the q=4 source-section cylinder, or prove it is not on the blank-root orbit.
- Audit the corrected double-B-to-A residue cylinder and close the remaining B-to-E/B-to-B residue classes with source-exact proofs. A separate, uncompiled canonical regular-E closure candidate in [ExceptionalESafeCanonical.lean](../agent37-d-timing-cocycle/ExceptionalESafeCanonical.lean) covers DRegular inputs `L(3*k+4,q,1)` for q=1 (via Agent 25's verified `q1b1_rejoins_regular`) or q≥2 with q≢1 (mod 3); its wrapper is [ExceptionalEReentryClassification.lean](../agent37-d-timing-cocycle/ExceptionalEReentryClassification.lean). For q≡1, the first E output has p≡2 and enters the marker P2-reset problem. The full q≥2 slice `a=9*t+10` has a submitted `ExceptionalEPacketClosure.exceptional_EA_all_reentry` source composition, including its q≡1 AP2 p=2 branch; the AP2 leaf compiled in CI 43315114860, but the full wrapper audit remains pending, so do not count this as fully verified. The remaining P2-reset/B-to-E/B-to-B obligations are for general `a=3*k+4` outside that and other specialized source cylinders.
- Integrate the conditional return cylinders into a complete physical blank-root invariant or produce a genuine blank-root witness.
- Determine all remaining six-state machines and prove the exact maximum primitive step count. Nothing in this dossier supplies a universal BB(6) upper bound or an exact champion score.


## Canonical DRegular bridge for the double-B A-marker closure (submitted; CI pending)

EChainDoubleBReentry.lean strengthens the A-marker endpoint theorem with an explicit unary-prefix floor. For every A-marker parameter ka, the returned unary prefix n satisfies n ≥ 2*(4*ka+3)+5, so it is safely in the a≥2 domain of the DRegular source-section representation. The module then converts all three exact A-marker endpoint shapes—including the trailing-false observational case—to a canonical DRegularSource.sourceSection and proves DRegular.Canon.

The resulting double_B_to_A_source_reentry theorem composes the two corrected B packets with the suffix parameter p unchanged through both edges, then applies the marker-A closure and returns a canonical DRegular source section. chain_double_B_to_A_source_reentry additionally composes any E-chain satisfying 1+4*8^d*h=27*t+17; its output is directly suitable for Agent25RootChain.extend_regular, rather than stopping at the intermediate regularEndpoint predicate.

The module is added to the manual agent37-p2-k13.yml kernel audit immediately after EChainDoubleBExit. It is a submitted source-level candidate until that workflow succeeds; no BB(6) conclusion follows from this local closure alone.


The same module also adds reset_double_B_to_A_source_reentry: it composes the P2 e_two_reset theorem, the arbitrary-depth E chain, two B packets, and the marker-A closure. Its hypotheses are the exact 3-adic reset identity, the E-to-BB index identity, and the E-chain resource bound. This remains a submitted source-level candidate until the existing manual audit succeeds.

## Depth-three P2 cylinder aligned with L(24956,2,2)

D3SecondReturnAlignment.lean kernel-checks an explicit depth-three arithmetic alignment. For every v≥0, set s=s₀+3⁸⁷v, k=729s+310, Q=3, h=54s+23, t=4096s+1744, and k_A=64t+45. The P2 reset, three E steps, two B edges, and A marker have the exact endpoint index

A=8*k_A+28=24956+3^87*(1315608+2^21*v).

This is the 86-step input lift of L(24956,2,2) with shift parameter 3*(1315608+2^21*v). The L(24956,2,2) → q=5 E-exit trajectory is now locally kernel-checked in the DRegular model, together with its exact quadratic time shift for every member of the depth-three family; see Seed24956ModelCheck.lean. The base run, base time, and polynomial coefficients have no Lean axioms, while the all-v shifted run/time theorems use only [propext, Classical.choice, Quot.sound], with no sorryAx. The reset/E/B/B original-source composition, its DRegularSourceShift transport, and the safe-E wrapper remain uncompiled. This is prepared-packet/model progress, not blank-root reachability.

The same congruence construction appears to extend to every odd E-chain depth d: take Q=3(d−1)/2 and h_d=41,23,5 for d≡1,3,5 (mod 6), respectively, then choose s in the unique residue class modulo 3^87 aligning the A endpoint with 24956. The explicit general formula and its current proof status are in D3SecondReturnAlignment.md; only d=3 has a checked Lean arithmetic artifact at present.
