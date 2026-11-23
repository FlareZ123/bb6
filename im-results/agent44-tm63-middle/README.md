# TM63 source rows 32–37 and authentic-root middle-34 continuation

**Status (2026-11-23):** The repository contains a source-level blank-root TM63 continuation through middle row 34, a source-level composition through the complete SectionResult dispatcher to index one and the outer-LC_Inc reset frame, and a source-only composition of that frame with the canonical marker-1 S0 endpoint. A separate row-35–37 extension and a direct arbitrary-A q4Tail-to-terminal composition also exist. None of the authentic-root/terminal chains is yet accepted by the focused Lean gate. The latest middle34 run (45281362511) moved past the stale OuterLCIncPrelude archive copy after the live-source override, then exposed the next dependencies in M0OddResidueSeven and M2EvenResidueTwo. The maintained M0 source and M2 source have now been selected explicitly by workflow overrides; the M0 helper/coordinate repairs are source edits only and await a fresh compile. The conditional exact score identity has a paper-level four-scale tower-tail refinement, but the authentic itinerary and exact primitive-step score remain unaccepted; the universal six-state upper bound remains open.

## Generic source increments and the authentic root

Let \(R=\texttt{tm63RootResidueSixK}\). The maintained root module TM63RootMiddle34.lean composes rows 27–34. Its decisive rows are:

| Row | Input marker | Input index | Source theorem |
|---:|---:|---:|---|
| 32 | 1 | \(16R-16\) | m1EvenValuation_counted_increment_source |
| 33 | 0 | \(16R-17\) | m0Odd_counted_increment_source |
| 34 | 2 | \(16R-18=8(2R-3)+6\) | m2EvenSix_generic_counted_increment_source |

The row-32 theorem factors every positive bounded index into an odd factor times a power of two and discharges the complete counted increment without a valuation side condition. Row 33 is the generic odd marker-0 increment. Row 34 is the all-parameter marker-2 even-six increment.

TM63RootMiddle34.lean defines the exact accumulated cost tm63MiddleFirst34Moves and proves

\[
\operatorname{run}\ tm2\ \texttt{tm63MiddleFirst34Moves}\ \texttt{blank}
=
\operatorname{some}\bigl(s1Config\ \texttt{tm63Length1}\ (16R-19)\ 1\
\texttt{tm63MiddleAfter34A}\ 0\ \texttt{tm63MiddleAfter34B}\
\texttt{tm63MiddleAfter34Head}\bigr).
\]

The main theorem is tm63_blank_reaches_after_middle34; it has no extra row-32 hypothesis. This is a source-level root-prefix statement, not a halt witness.

A separate direct extension, TM63RootMiddle37.lean, appends three more source increments:

| Row | Input marker | Input index | Source theorem |
|---:|---:|---:|---|
| 35 | 1 | \(16R-19=8(2R-3)+5\) | m1ResidueFive_counted_increment_source |
| 36 | 0 | \(16R-20=8(2R-3)+4\) | m0Even_residue4_counted_increment_source |
| 37 | 2 | \(16R-21\), odd | m2Odd_counted_increment_source |

It states tm63_blank_reaches_after_middle37, ending at index \(16R-22\), marker 1. This direct row-35–37 extension is still an uncompiled draft and is not part of the current acceptance target.

## Index-one reset frame and the actual terminal boundary

TM63RootAfterSectionResultToOne.lean takes the middle-34 root state through the complete 24-class SectionResult dispatcher to index one, marker two, then applies outerLCInc_full_run. Its theorem tm63_blank_reaches_after_middle34_reset_frame reaches state 3 with the exact nested outerLCIncPostludeTape. The current manual acceptance target includes this root module and audits its exported theorem profile.

The next pointwise identification is drafted in im-results/agent42-outer-lcinc/OuterLCIncCanonicalEndpoint.lean. For \(n=1,m=2\), the exact source-run cost is \(12a+71+3b\), and the file proves at source level that the nested frame is the canonical marker-1 S1/S0 endpoint:

\[
s1Config\ L\ 0\ 1\ (a+b+2)\ (2^b-1)\ 0\ (h+3b+5),
\]

equivalently the S0 tape encoding with left word markerWord 1 ++ d0 ++ d1pow L ++ lh and right counter \(z=2^b-1\). The generic endpoint theorem proves the width/value bound, and the root-specific lower bound is now source-drafted as `tm63Middle34Result_right_ge_two` / `tm63Middle34Result_z_ge_three` in `TM63RootMarker1Endpoint.lean`. This proof is uncompiled and must be included in the later endpoint acceptance target before applying the positive-z q4 macro. The declarations outerLCIncPostludeTape_eq_s1Config_m2 and outerLCIncPostludeTape_eq_marker1S0_m2 are not yet in the acceptance closure and have not been Lean-compiled or axiom-audited.

The new [TM63RootMarker1Endpoint.lean](TM63RootMarker1Endpoint.lean) composes `outerLCIncPostludeTape_eq_marker1S0_m2` with `tm63_blank_reaches_after_middle34_reset_frame`. Its theorem `tm63_blank_reaches_after_middle34_marker1_s0` states the resulting authentic blank-root run directly at the canonical marker-1 S0 input, with width (A=\texttt{middle34Result.exponent}+\texttt{middle34Result.right}+2), right counter (z=2^{\texttt{middle34Result.right}}-1), and the exact final head. It also imports the generic width/value bounds. This integration is **uncompiled source draft**; it does not establish halting or close the positive-(z) q4 macro.

**Additional interface blocker identified during source review (not yet a Lean diagnostic):** `outerLCInc_s1_postlude_run` returns a postlude frame over `outerLCIncSourceT3 T h a m r`, and `outerLCInc_preHRun` reaches that same T3 tape. But the current `outerLCInc_full_run` statement in `OuterLCIncPostludeSource.lean` appears to claim the frame over the original S1 tape `T`. The postlude tape is a finite frame over its input and preserves the far-left cells; T3 has already changed the left-facing source word. The root wrapper currently repeats the original-T output, while the canonical endpoint lemma expects T3. The source-level corrections are now on main: commit `86234f2921213492c4913dee3c21e4a1d81f3ba9` carries the existential `r` and T3 tape through `outerLCInc_full_run`; commit `7392c1309c6e393fbbff7868086d9e89be3db47d` carries the same T3 output (with (r=0)) through `TM63RootAfterSectionResultToOne.lean`; and commit `77532044a15f7a00bcac3e68eff197836eae08b4` preserves the `v2 n = r` witness returned by `outerLCInc_preHRun` when normalizing the prelude run and composing it with the postlude. Commit `6aa37091aea02f8bcbeca4bfcc72428e49175b3d` reduces the `Option.bind (some ...)` left by `run_add` with `Option.bind_some` in the final composition proof. Agents 42 and 48 have been asked to review these edits. They remain **uncompiled source corrections** pending exact local preflight; do not treat the new root-marker1 wrapper as type-checked.

The current root wrapper has \(L=\texttt{tm63Length1}=76\): tm63FirstSection.exponent is nextExponent 2 6 63 = 71, and tm63Length1 = 3 + 71 + 2. The source lemma tm63Length1_even is in TM63Length1Parity.lean. The authentic endpoint also has \(z=2^b-1\ge3\), so the marker-1 experiments that set \(z=0\) do not directly close the root. In particular, the exact z=0 even-L terminal law is not a positive-z theorem. The positive-z q4 nested-counter macro, its cycle recurrence, and the final halt remain open.

## Direct arbitrary-A q4Tail-to-terminal dispatcher (new source draft)

A new route appears to bypass the positive-z P2 postlude and the repeated q4Tail outer-width recurrence. It generalizes the A=2 terminal reparameterization to every A>=2.

For the authentic q4Tail input, set
- w=A+L+1 and q=firstQ4P1Value L A;
- W=A+L+2 and N=firstQ4P1M L A-3=2^W-2^A-3;
- K=2^z+z+3, n=2^(2^z-1), and H=3*2^z+3*z+9+3*n.

The residual identity is
`p2ResidualLeft m (q4TailS0Tail w q) = d1pow K ++ markerWord 0 ++ d0 ++ binDec W N ++ lh`,
with
`binDec W N = d0 ++ d1 ++ d0pow(A-2) ++ d1 ++ d0pow(L+1)`.
After the existing q4Tail-to-S0 adapter and carry-prefix rewrite, the authentic q4Tail frame is exactly
`s1Config W N 0 (K+n-1) (2^(n-1)-1) 0 H`.
The existing counted drain and complete 24-class SectionResult dispatcher then apply. If L is even, N is divisible by 3, so the dispatcher returns to marker zero and the terminal SectionBits macro applies.

For the root, L=tm63Length1=76 is even and A=rootMarker1A>=2, so W=rootMarker1A+78 and N=firstQ4P1M 76 rootMarker1A-3. This is a direct arbitrary-A route; it does not require reducing A to 2 or re-entering the q4Tail recurrence after the tail has changed to 111111. At A=2 it specializes to W=80 and N=2^80-7, recovering the existing A2 terminal instance.

Source drafts added under this directory:
- GeneralQ4TailDispatcherReparam.md — derivation and exact implementation target.
- GeneralQ4TailArithmetic.lean — arbitrary-A BinDec shape and mod-3 lemmas.
- GeneralQ4TailS1Reparam.lean — residual and S0/S1 tape reparameterization.
- GeneralQ4TailS1Config.lean — q4Tail frame equals the S1 dispatcher input.
- GeneralQ4TailTerminalComposition.lean — counted drain, complete dispatcher, terminal SectionBits.
- The authentic root wrapper is maintained by Agent 42 at `im-results/agent42-q4-s0-drain/TM63GeneralQ4TerminalComposition.lean`; it states `tm63_blank_halts` and `tm63_blank_attainable` using this directory's terminal theorem.
- check_general_q4tail_reparam.py — standalone script covering 18 exact-TM2 cases (L in {4,6,76}, A in {2,3,4}, z in {1,2}) of the S0/S1 tape identity and counted-drain endpoint.

**Status:** all six artifacts are source drafts and have not been Lean-compiled or axiom-audited. The direct root theorem is therefore a promising composition target, not an established halting proof. The last middle34-acceptance run (44438791470) failed in an older M1EvenState1Sweep revision because it lacked the hne3 side condition; the current file was repaired later in commit 3b4787ea94 (2026-11-19T11:30Z), so that CI failure is stale. The repaired root prefix still needs a fresh accepted build. The direct route also continues to depend on the complete 24-class source dispatcher, including the M0 and M2 zero-row families. Local shell/Python/container execution failed with ClientError; do not substitute CI for the required local preflight. The existing positive-z P2 postlude route remains available as an alternate path until this route is accepted.

Immediate priority: compile the short arithmetic and S0/S1 reparameterization modules, then the counted-drain/dispatcher composition, then the root shift composition. Audit the complete transitive closure for only the repository's accepted axioms; do not move this material into results/ before that gate passes.

## Conditional four-scale score refinement

A geometric-series argument sharpens the general dispatcher-tail bound to \(0\le E_r<45b_{r-1}^2\) whenever \(2\le r\le N\) and \(N\le b_{r-1}\). At the authentic index, this gives
\[
S=6b_N^2+54b_N+6b_{N-1}^2+57b_{N-1}
 +6b_{N-2}^2+69b_{N-2}
 +6b_{N-3}^2+81b_{N-3}
 +39b_{N-4}+192+E_4,
\]
with \(0\le E_4<45b_{N-4}^2\). The residual is quadratic in the first omitted tower variable, improving the earlier bound by an exponential scale. This is a paper-level consequence of the conditional score identity, not a compiled Attainable theorem. Full derivation: [TM63TowerTailExpansion.md](TM63TowerTailExpansion.md).

## Focused Lean acceptance

The existing manual-only target middle34-acceptance in .github/workflows/agent42-champion-terminal-source.yml is the acceptance path. It reconstructs the authoritative terminal imports, then compiles the exact dependency closures of these five roots:

1. im-results/agent48-counted-inc0/M1EvenValuationSource.lean
2. im-results/agent44-tm63-middle/M2EvenSixGenericCounted.lean
3. im-results/agent44-tm63-middle/TM63RootMiddle34.lean
4. im-results/agent48-counted-inc0/TM63RootAfterSectionResultToOne.lean
5. im-results/agent48-counted-inc0/Q4S0FirstCycleMacros.lean

**Live-source selection and current blockers:** TerminalProofs.tar.xz.b64 contains older copies of several source modules. Run 44933359496 failed in the embedded OuterLCIncPrelude at the d1pow boundary-cell proof and final counted_LBinDec_HRun coordinate alignment. The maintained im-results/agent8-counted-reset/OuterLCIncPrelude.lean fixes these with outer_sideBit_append_shift at offset zero and explicit hbase/hhead normalization. Run 45281362511 moved past that module, then failed in M0OddResidueSeven.lean and M2EvenResidueTwo.lean. The M2 diagnostic was an unqualified q4LeftFacing ambiguity; the maintained M2 source already qualifies the namespace, so the workflow now overrides M2EvenResidueTwo to that file. The M0 source had missing local helpers, a prefix-length metavariable, an unnormalized bridge configuration, an unnecessary simp-at-equality, and a tape/config normalization omission; the current source now supplies the copied local helpers, fixes the prefix index and bridge orientation, uses constructor equality elimination, and normalizes T explicitly. The workflow now overrides M0OddResidueSeven to the maintained file as well. These are source repairs and source-selection changes, not compile acceptance.

It audits 14 exported declarations, including the two generic counted increments, the middle-34 root theorem, the complete SectionResult dispatcher, the index-one marker-two theorem, the reset-base prefix/suffix, the nested-frame root theorem, and outerLCInc_target_binary_prefix. The accepted foundational axiom set is {propext, Classical.choice, Quot.sound}; sorryAx and native_decide are rejected. This is a focused manual job, not a per-commit workflow.

The latest focused acceptance sequence has three relevant stages:

- Run 44933359496 (2026-11-21, head e28a5b5…) failed in the stale OuterLCIncPrelude.lean embedded in TerminalProofs.tar.xz.b64. The maintained source now fixes the boundary-cell proof and H-run coordinate normalization; the workflow override selects it.
- Run 45281362511 (head 1138ef3b…) moved beyond OuterLCIncPrelude, then failed in M0OddResidueSeven and M2EvenResidueTwo. Run 45284871207 tested the first repairs and exposed additional support lemmas needed by the local counted-left-sweep proof, plus a remaining s1Config/tape normalization. It also exposed M0EvenEightValuationEncoding and M2EvenResidueSix as separate blockers. The current source now adds the missing M0Odd support lemmas, repairs the M0Even8 fixed-prefix decomposition and v2 namespace, and imports Q4Suffix explicitly for M2EvenResidueTwo. The M2-even-six branch now has a new public exact-tape interface, m2EvenSix_q4_prefix_data_exact, proving the existential prefix witness equals the explicit cut tape by function extensionality; M2EvenResidueSix.lean has been updated to consume it instead of the invalid rfl across an opaque existential. This is a source-level repair only, not compile acceptance. The maintained M2-even-six source has now been patched with a local source-left suffix, a local counted-left-sweep head helper, the existing residue-six config extensionality helper, qualified Agent8Q4Suffix names, explicit prefix index, normalized bridge rewrite/orientation, constructor equality elimination, and pow2_mul_pow arithmetic identities. Its existential tape consumers now use m2EvenSix_q4_prefix_data_exact. The targeted live-source compile (workflow agent48-m2-even-six.yml, run 45288313701) compiled M2EvenSixQ4Prefix, including the new exact-tape theorem, and reached M2EvenResidueSix. It failed later on two tape-coordinate normalizations, a remaining omega bound, two run-composition rewrites, a head-bound arithmetic mismatch, and the final lifted-config shape. The first two tape normalizations and the right-facing namespace qualification have since been patched. A further source patch adds hSweep', explicitly normalizing the counted sweep's s1Config input before run_add composition in both bridge and E-scan branches; this directly addresses the failed rewrite pattern. The remaining proof obligations are not yet compiler-accepted. Do not claim the dependency resolved or re-run unchanged.

Older M1 failures remain historical: run 44424308953 exposed tape-extensionality goals, and run 44438791470 retained h - 1 + (-1) instead of h - 2. Commits 9103e64b22f72afae47f53e8963426ff7db93bc3 and 3b4787ea945e2d0d1c6302412957b6e21dd4ef6f contain the corresponding arithmetic repairs. No source-closure acceptance or axiom-audit claim is made until the updated focused target passes.

## Next proof actions

1. The preferred check is exact local Lean 4.36.0-rc2 preflight. The current invocation's prescribed bootstrap returned a tool-level ClientError before executing, so the existing manual workflow is the constrained fallback.
2. The next middle34-acceptance run should test the maintained OuterLCIncPrelude, M0OddResidueSeven, and M2EvenResidueTwo files selected by explicit overrides. Inspect only the first new compiler diagnostic. Do not repeat the stale-archive failure or dispatch unchanged inputs.
3. If it passes, record all 14 exported axiom profiles and preserve the root-to-nested-frame boundary exactly as proved.
4. Only after that acceptance, add a separate narrow manual acceptance target for TM63RootMiddle37.lean, OuterLCIncCanonicalEndpoint.lean, and TM63RootMarker1Endpoint.lean; do not widen the current target before it passes.
5. Formalize the root-specific bound `middle34Result.right ≥ 2` (hence `z ≥ 3`), then compile and axiom-audit the arbitrary-A terminal route in `GeneralQ4TailArithmetic.lean`, `GeneralQ4TailS1Reparam.lean`, `GeneralQ4TailS1Config.lean`, `GeneralQ4TailTerminalComposition.lean`, and Agent 42's `TM63GeneralQ4TerminalComposition.lean`. After `tm63_blank_reaches_second_q4_tail`, this route needs no further q4Tail/P2 recurrence.

All material described here remains in im-results/ until it meets the repository's academically publishable results/ standard. No exact BB(6) value, complete champion halt count, or universal six-state upper bound is established.

## 2026-11-21: direct q4-terminal source-acceptance correction

The existing manual `middle34-acceptance` target is a narrower acceptance target for five earlier roots. It does **not** compile `im-results/agent42-q4-s0-drain/TM63GeneralQ4TerminalComposition.lean` or its direct arbitrary-A q4Tail/S0-to-terminal closure. A passing middle34 run must not be reported as acceptance of the direct q4-terminal route.

The actual root-to-terminal target is `im-results/agent42-q4-s0-drain/TM63GeneralQ4TerminalComposition.lean`. Its full dependency closure is approximately 192 modules. The exact staging and `lean_compile_closure.py` command, including the extracted terminal source root and `TerminalBridge` override, are recorded in `im-results/agent42-q4-s0-drain/2026-11-21-lean-closure-repairs.md`. Do not dispatch CI as a substitute for the required local RC2 preflight.

The first small source slice is `im-results/agent48-counted-inc0/M1EvenValuationBridge.lean`. It now imports `ChampionRootBridge`, `M1EvenState1Sweep`, `M1EvenState5Sweep`, and `CountedSweep` directly (plus `Lean.Elab.Tactic.Omega`); its unnecessary `CountedQ4Prefix` import and `Agent6Q4Prefix` open were removed. A proposed minimal preflight is:

```sh
python3 tools/lean_compile_closure.py \
  im-results/agent48-counted-inc0/M1EvenValuationBridge.lean \
  --workdir /tmp/m1-bridge-acceptance \
  --jobs 4
```

An independent finite smoke test is now stored at `M1EvenValuationSourceSmoke.mjs`. An equivalent JS simulation checked 252 small parameter tuples (`len=1..3`, all `q<2^len`, `v=0..2`, `a=1..2`, `b=0..2`); every run matched the claimed reset-prefix step count, final state/head, and full S1 output tape. This is finite computational evidence only, not a proof or Lean acceptance.

Current invocation tool status: local `container.exec`, `python.exec`, and `python_user_visible` fail with tool-level `ClientError` before executing commands. The two attached split archives have metadata sizes 304,196,898 bytes each, totaling 608,393,796 bytes; this is consistent with the official 608,393,640-byte RC2 Linux tar.zst member plus 156 bytes of outer-ZIP overhead, but is not an integrity test. Correct extraction is outer `unzip`, then `tar --zstd -xf /tmp/lean/lean-4.36.0-rc2-linux.tar.zst -C /tmp/lean`, then set PATH and run `lean --version`.

**Status remains unaccepted:** no local Lean compilation, no exported axiom audit, and no theorem establishing the exact BB(6) value or a universal upper bound.


## Root row-32 M1 counter: exact valuation and output word (2026-11-21)

Let (A=tm63FirstSection.exponent). The established facts (A\ge5) and (A\equiv1\pmod2) imply (A\ge7). From
[
tm63RootMiddleK=31\cdot2^{A-3}-1,
\qquad
tm63RootResidueSixK=tm63RootMiddleK/2,
]
we obtain
[
R:=tm63RootResidueSixK=31\cdot2^{A-4}-1,
\qquad
n_{32}:=16R-16=31\cdot2^A-32.
]
In particular, the row-32 M1 counter has the exact factorization
[
n_{32}=(2q+1)2^5,
\qquad
q=31\cdot2^{A-6}-1,
\qquad
\ell=A-1,
\qquad
\ell+1+5=tm63Length1.
]
The bound (q<2^\ell) is immediate from (31<32). Thus this row has **exact 2-adic valuation five**, not merely an arbitrary positive valuation. It can instantiate the existing factorized theorem `m1EvenValuation_counted_increment_source_factorized` directly.

The encoding gives a further exact head-facing word identity. Since
[
q=(2\cdot15+1)2^{A-6}-1,
]
the existing `binDec_sub_one_carryPrefix` and `binDec_max 4` identities yield
[
binDec(A-1,q)
=d0pow(A-6)\mathbin{++}d1\mathbin{++}d0pow(4).
]
Consequently the row-32 output counter has
[
binDec(tm63Length1,n_{32}-1)
=d0pow(5)\mathbin{++}d1\mathbin{++}d0pow(A-6)
 \mathbin{++}d1\mathbin{++}d0pow(4).
]
This is an exact algebraic specialization of the existing source encoding, not an independent Lean-accepted source theorem. The current root wrapper still calls the general valuation-parametric theorem; use the explicit factorized instance only if it materially simplifies the root proof or its trust profile. No local Lean compile was available in the 2026-11-21 invocation.


The same factorization exposes the next row-34 input word. Put (q=31\cdot2^{A-6}-1) as above. Then
[
16R-18
=2\bigl((2q+1)2^4-1\bigr),
\qquad
(2q+1)2^4-1=8R-9.
]
Using `binDec_even` for the outer factor 2 and `binDec_sub_one_carryPrefix` with (r=4) for the inner decrement gives
[
binDec(tm63Length1,16R-18)
=d1\mathbin{++}d0pow(4)\mathbin{++}d1
 \mathbin{++}d0pow(A-6)\mathbin{++}d1\mathbin{++}d0pow(4).
]
Here (tm63Length1=A+5). This is the exact head-facing binary counter word entering row 34 (the M2-even-six macro), not merely its parity/valuation class. The identity follows from the preceding row-32 word formula and the source encoder's two carry-prefix lemmas; it has not yet been added as a Lean theorem or locally compiled.


## Six-row root residue pattern (rows 32–37)

The same (R=tm63RootResidueSixK) identity explains the exact source-class sequence used by the middle continuation. Since (R=31\cdot2^{A-4}-1) is odd and (v_2(R-1)=1), the six consecutive input counters are:

| Row | Counter | Exact 2-adic class | Marker/source class |
|---:|---:|---:|---|
| 32 | (16R-16) | (v_2=5) | M1, even valuation |
| 33 | (16R-17) | odd | M0, odd |
| 34 | (16R-18) | (v_2=1), residue (6\pmod8) | M2, even-six |
| 35 | (16R-19) | odd, residue (5\pmod8) | M1, odd-residue-five |
| 36 | (16R-20) | (v_2=2), residue (4\pmod8) | M0, even-residue-four |
| 37 | (16R-21) | odd | M2, odd |

The valuations are immediate:
[
16R-16=2^5(31\cdot2^{A-5}-1),\
16R-18=2(8R-9),\
16R-20=4(4R-5),
]
and each displayed odd factor is odd. The intervening counters are odd. This gives a compact arithmetic explanation for why the root proof uses the sequence M1-even / M0-odd / M2-even-six / M1-odd-five / M0-even-four / M2-odd. It is a parameter-level source classification, not a replacement for the six Lean run theorems.


## Common-tail normal form for all six row inputs

The row-32/34 identities factor further. Set
[
Q_A:=d0pow(A-6)\mathbin{++}d1\mathbin{++}d0pow(4).
]
For (L=tm63Length1=A+5), the six consecutive input counters have the following exact `binDec` words:
[
\begin{array}{c|l}
32 & d1pow(5)\mathbin{++}d0\mathbin{++}Q_A\\
33 & d0pow(5)\mathbin{++}d1\mathbin{++}Q_A\\
34 & d1\mathbin{++}d0pow(4)\mathbin{++}d1\mathbin{++}Q_A\\
35 & d0\mathbin{++}d1\mathbin{++}d0pow(3)\mathbin{++}Q_A\\
36 & d1pow(2)\mathbin{++}d0pow(3)\mathbin{++}Q_A\\
37 & d0pow(2)\mathbin{++}d1\mathbin{++}d0pow(2)\mathbin{++}Q_A
\end{array}
]
These follow by applying `binDec_even`, `binDec_odd`, and the carry-prefix identities to the six arithmetic counters above; the shared tail (Q_A) is unchanged throughout the block. This is a compact normal form for the complete row-32–37 source segment and explains why the existing generic source lemmas fit the root parameters. The table is a derived synthesis; the existing per-row Lean theorems remain the formal run evidence.


## Exponential-window common-tail formula for the root counter

The 64-row identity is a special case of a formula for every prefix length (k\le A). Let (A=tm63FirstSection.exponent\ge7), (L=A+5=tm63Length1), and (R=tm63RootResidueSixK=31\cdot2^{A-4}-1). The root's initial middle counter is
[
tm63Index1=16R+15=31\cdot2^A-1.
]
After (r-1) unit decrements, the row-(r) counter is
[
n_r=tm63Index1-(r-1)=31\cdot2^A-r.
]
Fix any (k) with (1\le k\le A) and any (r) with (1\le r\le2^k). Define (E_k(r-1)) as the (k)-block word whose (i)-th block (least-significant bit first) is (d1) when bit (i) of (r-1) is (1), and (d0) when it is (0). Then
[
\boxed{
binDec(L,n_r)
=E_k(r-1)\mathbin{++}d0pow(A-k)
 \mathbin{++}d1\mathbin{++}d0pow(4).
}
]
The proof is the complement identity
[
2^{L+1}-1-n_r
=2^{A+5}+2^A+(r-1).
]
Since (r-1<2^k\le2^A), the low (k) bits are exactly (r-1), bits (k,\ldots,A-1) are zero, bit (A) is one, and bits (A+1,\ldots,A+4) are zero; the top bit (A+5) is the implicit terminator of `binDec`. The `binDec_even`/`binDec_odd` recurrences map these bits to the stated (d1/d0) blocks.

For (k=6), this gives a common tail (Q_A=d0pow(A-6)++d1++d0pow(4)) for the first 64 counters; rows 27–37 are the specific instances used by the current source composition. For (k=A), it gives the same final five blocks (d1++d0pow(4)) across a window of (2^A) consecutive counters, with the first (A) blocks encoding the row number. This is an exact source-encoding identity, not by itself a proof that all corresponding machine transitions have been composed.


### Formalization route via a low-block prefix lemma

For a Lean proof using the existing `binDec_even`/`binDec_odd` recurrences, set (B=A-k),
[
q_B=31\cdot2^B-1,\qquad s=2^k-r.
]
Then
[
n_r=q_B\cdot2^k+s,\qquad 0\le s<2^k,
\qquad L-k=B+5.
]
A generic lemma of the form
[
binDec((B+5)+k, q_B2^k+s)
=\operatorname{lowBlocks}_k(s)\mathbin{++}binDec(B+5,q_B)
]
follows by (k) applications of `binDec_even`/`binDec_odd). Since (s=2^k-1-(r-1)), its low-block code is exactly (E_k(r-1)). The remaining tail is a one-line carry-prefix instance:
[
binDec(B+5,31\cdot2^B-1)
=d0pow(B)\mathbin{++}d1\mathbin{++}binDec(4,15)
=d0pow(B)\mathbin{++}d1\mathbin{++}d0pow(4),
]
using `binDec_sub_one_carryPrefix 4 15 B` and `binDec_max 4`. This gives a reusable formalization path that avoids reasoning directly about the complemented integer's bit positions.


## Root-wide dispatcher-marker invariant: why q4Tail is still needed

The first-reset S1 root is in marker (m=2) with counter
[
n=tm63Index1=31\cdot2^A-1,
\qquad A=tm63FirstSection.exponent\text{ odd}.
]
Since (2^A\equiv2\pmod3) and (31\equiv1\pmod3), this gives (n\equiv1\pmod3), hence
[
I(m,n):=(m+2n)\bmod3=(2+2)\bmod3=1.
]
Every source increment preserves (I): its endpoint is ((m+2,n-1)\pmod3), so ((m+2)+2(n-1)\equiv m+2n\pmod3). Equivalently, the existing theorem `sectionResult_marker` states that the marker at index zero is exactly ((m+2n)\bmod3).

Therefore a complete `sectionResult_run_complete` countdown from the first-reset root, or from any intermediate row in this same source segment, ends at index zero with marker (1). The currently certified terminal bridge `s0_reset_sectionBits` is specifically for marker zero. The q4Tail reparameterization is not redundant: it constructs a new marker-zero, index-divisible-by-three terminal frame and changes the phase invariant needed by the terminal bridge.
