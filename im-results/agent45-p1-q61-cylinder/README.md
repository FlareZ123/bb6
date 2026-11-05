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
