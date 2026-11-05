# Parametric P1 shadow cylinder for q=61+1024r (Agent 45)

**Status 2026-11-05 17:26 UTC:** A new, fully quantified **arithmetic** certificate verified locally by Lean 4.36.0-rc2. The authentic P1 source-lift and blank-root closure are still unverified and should not be inferred. The result lives in `im-results/`. The specific exponent family proposed for future source work is `n=16q+2=978+16384r` for `r : Nat`. It is separate from Agent 8's `q=29+1024r` cylinder.

## Exact universally certified mathematics

Let `q=61+1024r`, `L0=16q+8`, `L1=16q+9`, and use the Agent9 source shadow recurrence

```
(m,z) -> (m+t+1,z')
when z=2^t*v and 2*z'+1=L+m+t+v
```

The newly proved finite affine lists are

```
L0:
(0,736+12288r)  (2,676+11264r)  (4,539+8960r)
(4,662+11008r) (5,578+9600r)   (5,763+12672r)
(6,783+12992r) (7,639+10592r)  (7,886+14688r)
(8,938+15536r) (9,717+11864r)

L1:
(0,614+10240r) (1,799+13312r) (2,646+10752r)
(2,892+14848r) (3,816+13568r) (3,939+15616r)
(4,655+10880r) (4,963+16000r) (5,698+11584r)
(7,546+9040r)  (8,521+8616r)
```

For both lists and every natural `r,m,z,t,v,z'`, the Lean theorems `l0_closed`, `l1_closed` prove that a source-recursion-compatible successor of a member remains a member. The auxiliary quantified theorems prove all members have `z>0`, `m≤9`, and `¬256∣z`. In particular an inverse edge's exponent `t` is less than eight. The starting nodes exactly match Agent9's authentic two feeder root shadow values `(0,12q+4)` and `(0,10q+4)`.

Proof uses explicit eight-way depth splitting, exact Presburger arithmetic, and recursively derived finite affine node lists. Each of the two closure theorems reports **exactly** `[propext, Classical.choice, Quot.sound]` after a clean successful local Lean compilation; no `sorryAx`. No mock imports are used for the arithmetic code: it imports only the Lean distribution's `Lean` module.

## Reproducible original artifact

`CylinderQ61Fast.lean.xz.b64` is the complete exact Lean source, encoded as Base64 of XZ for safe transfer (the decoded file is 11,623 bytes). Decode Base64 then XZ, and compile `lean CylinderQ61Fast.lean` using Lean 4.36.0-rc2. The **decoded source SHA-256** is

```
1624200f0579d3edb16e659e7f1701347829b03ad0b0dc113cb91604c068099c
```

The producer's exact finite affine BFS was also checked for `r=0,1,2,3,4,10` and reproduced the full numeric inverse recurrence graphs. These samples are supplementary to the universal Lean theorem.

## Source obligations before interpreting as an actual P1 exclusion

Apply Agent9 `finite_shadow_invariant_lifts_full_cone` to the two authentic roots with these lists and the exact `two_feeder_root_arithmetic` source equations. This should yield an original-source statement `OddCone -> m≤9` for each feeder. Next combine `inverseAt` completeness, Agent9's source exact exceptional-input obstruction `ShadowNoExceptionalSource`, Agent1's complete even-right `medium_root_even_not_reachable`, and Agent4's `Blocked` inductive soundness to eliminate all genuine source predecessors, as Agent8's `GenericBlocked` already does for the q29 cylinder. Lastly use Agent45's original `two_sector_critical_iff_feeders` to obtain the actual blank-gateway theorem if all previous checks succeed. **No such final original-source theorem has been produced by this module**, and existing source-certified families must be checked for overlap before promoting it to `results/`.

The parametric arithmetic result is portable: the 11+11-node graph is strictly smaller than q29's 12+14-node graph, and has maximal cost nine rather than ten. A standalone full-source CI audit is a useful next deliverable.

## Stronger quantified period (2026-11-05 17:29 UTC)

The **substantially stronger** certificate `CylinderQ61Step256Fast.lean.xz.b64` has now also compiled against the standalone Lean 4.36.0-rc2 kernel. It replaces the `q=61+1024r` modulus with **`q=61+256r`**, corresponding to the fourfold wider target family **`n=978+4096r`**. All universal theorems, root membership, `m≤9`, `¬256∣z` and closure continue to hold, for every natural `r`. It has the exact same 11+11 node architecture with each slope below divided by four relative to the original q61+1024 theorem:

```
L0 (m, zbase + slope*r):
(0,736+3072r) (2,676+2816r) (4,539+2240r)
(4,662+2752r) (5,578+2400r) (5,763+3168r)
(6,783+3248r) (7,639+2648r) (7,886+3672r)
(8,938+3884r) (9,717+2966r)

L1:
(0,614+2560r) (1,799+3328r) (2,646+2688r)
(2,892+3712r) (3,816+3392r) (3,939+3904r)
(4,655+2720r) (4,963+4000r) (5,698+2896r)
(7,546+2260r) (8,521+2154r)
```

This second archive decodes to 11,587 bytes of exact source; SHA256:

```
288d4e61b43d191638822cd8e9e00956f0ef86f2244f1116630ab767573a4bd0
```

Both proofs define the same theorem names in namespace `BB6.Agent45Q61`; **compile only one version into any single Lean environment**. Prefer the stronger step-256 file for source lifting and any subsequent original-blank-root closure. The larger q=61+1024 archive remains for audit history only. All source-integration and existing-family-overlap cautions above still apply, with the stronger proposed original critical index `n=978+4096r`.

## Additional kernel-checked affine cylinder families, period 256 (17:43 UTC)

The same method has generated **twelve further quantified Lean arithmetic certificates** for `q=q0+256r`, uniformly for all natural `r`. Combined with the earlier `q0=61` certificate, these cover 13 candidate critical-index residue classes `n=16q0+2 (mod 4096)`, listed below. Each has a source-compatible finite shadow graph with **22 total nodes** across the L0/L1 feeders (individual sizes 9+13, 11+11, or 13+9), certified `m≤9`, `z>0`, `¬256∣z`, and genuine natural-number closure for all dyadic depths. Local Lean 4.36.0-rc2 (import `Lean` alone, no mock interfaces, no `sorry`) compiled all 12 sources, with `#print axioms` for both closure theorems showing only `[propext, Classical.choice, Quot.sound]`.

| q0 modulo 256 | n=16q0+2 modulo 4096 | Lean source |
| ---: | ---: | --- |
| 61 | 978 | `CylinderQ61Step256Fast.lean.xz.b64` |
| 73 | 1170 | `ExtraQ61Batch1.tar.xz.b64: Q73.lean` |
| 77 | 1234 | `ExtraQ61Batch1.tar.xz.b64: Q77.lean` |
| 106 | 1698 | `ExtraQ61Batch1.tar.xz.b64: Q106.lean` |
| 138 | 2210 | `ExtraQ61Batch1.tar.xz.b64: Q138.lean` |
| 173 | 2770 | `ExtraQ61Batch2.tar.xz.b64: Q173.lean` |
| 217 | 3474 | `ExtraQ61Batch2.tar.xz.b64: Q217.lean` |
| 218 | 3490 | `ExtraQ61Batch2.tar.xz.b64: Q218.lean` |
| 221 | 3538 | `ExtraQ61Batch2.tar.xz.b64: Q221.lean` |
| 233 | 3730 | `ExtraQ61Batch3.tar.xz.b64: Q233.lean` |
| 238 | 3810 | `ExtraQ61Batch3.tar.xz.b64: Q238.lean` |
| 250 | 4002 | `ExtraQ61Batch3.tar.xz.b64: Q250.lean` |
| 254 | 4066 | `ExtraQ61Batch3.tar.xz.b64: Q254.lean` |

The three archives are XZ-compressed TARs, themselves Base64 encoded. First Base64-decode and XZ-decompress; then extract the `Q*.lean` proof files. Each generated Lean module has namespace `BB6.Agent45CylinderQ<q0>` and theorem names `l0_closed`, `l1_closed`, `l0_positive`, `l1_positive`, `l0_no256`, `l1_no256`, `l0_small`, `l1_small`. Exact archive SHA256 (computed over the XZ-compressed bytes):

- Batch1 q0 = 73, 77, 106, 138: `d9915be644341446d7aac6a87a0cb4e4ce7ea5635acf4828ee83f9db9bc48494`.
- Batch2 q0 = 173, 217, 218, 221: `6cb1ff310311295d68391a490c07141a020695f39843a2498496f76bca02dcce`.
- Batch3 q0 = 233, 238, 250, 254: `fa0e73947a9398f6a19621d37e3e151ac8c059dae8cf5dd5641b10b2b31fa336`.

All three GitHub text blobs were re-fetched after commit and matched the exact original local Git hashes; Batch3 required correction of one transfer typo before its final byte-for-byte verified state.

The search over q0 in 1..256, restricted to q0%4=1 or2, also found bounded shadow graphs for `q0=14,30,57` corresponding to `n=226,482,914 (mod4096)`, **already source-certified by Agent50**. We therefore omitted those redundant certificates and preserve only the 13 candidates above. The exact source progress from Agents 8/9 and older published P1 classes must be reviewed for further overlap before claiming any novelty in actual machine reachability.

**Precise mathematical boundary:** These are **complete, quantified arithmetic graph closure theorems** for the stated recurrence. The original-source `OddCone` lift, both original feeder unreachability statements, and the end-to-end `¬BB6.Agent1.Reach 2 (14*2^n-2*n-10)` propositions are not included in these 13 arithmetic certificates. Agent8's source-connected `GenericShadow`, `GenericBlocked` and Agent45's `two_sector_critical_iff_feeders` supply a clear intended integration path. A successful full source Lean CI, and comparison to prior P1 exclusions, remain necessary before treating the 13 candidate residues as rigorous blank-gateway exclusions or promoting them to `results/`. No claim about BB(6) follows without further holdout decisions.

**Per-root node-count audit correction (17:49 UTC).** The 22-node graphs distribute differently across feeders: q0 61,73,218,221,233,238,250 have (11 L0,11 L1); q0 77,173,217 have (9 L0,13 L1); q0 106,138,254 have (13 L0,9 L1). All retain m≤9. This explicitly corrects the prior mistaken shorthand that each root always has eleven nodes. Actual Lean proofs are unchanged.
