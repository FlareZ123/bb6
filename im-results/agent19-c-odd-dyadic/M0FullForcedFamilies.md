# m=0 full-forced infinite families

Status: eleven infinite progressions are formalized in committed Lean source. The original-source CI run 42401719081 stopped at M0Mod8Three. That module's gate namespace, target-coordinate transfer, and Boolean-filter proof have since been repaired. Four further progressions were added after that run. The complete eleven-family source audit is pending the next phase run. Treat all claims below as provisional until the new run completes and every theorem audit is free of `sorryAx`.

All targets below are the exact m=0 high stopping targets
`(2*j+3, 4*(j+3)-(j+5)) = (2*j+3,3*j+7)`.
The four-sector normalizer uses the source gates in this order: odd-low, even-seven, even-affine, six-even-right. Every listed terminal pair has odd right coordinate at least 5 and coordinate sum congruent to 1 or 2 modulo 4. The source theorem `fullForcedExcluded_sound` then rules out every blank-derived section hit.

| Parameter progression | Exact target | Forced inverse path | Terminal pair | Terminal sum mod 4 |
|---|---|---|---|---:|
| `j=8t+3` | `(16t+9,24t+16)` | even-affine | `(40t+23,12t+7)` | 2 |
| `j=16s+2, s≥1` | `(32s+7,48s+13)` | odd-low | `(40s+8,44s+9)` | 1 |
| `j=32t+6` | `(64t+15,96t+25)` | odd-low → six-even-right | `(168t+36,44t+9)` | 1 |
| `j=64t+58` | `(128t+119,192t+181)` | odd-low → even-seven | `(168t+153,172t+157)` | 2 |
| `j=32t+21` | `(64t+45,96t+70)` | six-even-right → six-even-right → even-affine | `(232t+159,12t+7)` | 2 |
| `j=32t+15` | `(64t+33,96t+52)` | even-affine → odd-low | `(104t+52,76t+37)` | 1 |
| `j=128t+71` | `(256t+145,384t+220)` | even-affine → odd-low → six-even-right → six-even-right | `(872t+484,76t+41)` | 1 |
| `j=128t+5, t≥1` | `(256t+13,384t+22)` | six-even-right → six-even-right → even-affine → odd-low | `(488t+20,268t+9)` | 1 |
| `j=512t+357` | `(1024t+717,1536t+1078)` | six-even-right → six-even-right → even-affine → odd-low → six-even-right → six-even-right | `(3560t+2476,268t+185)` | 1 |
| `j=512t+406` | `(1024t+815,1536t+1225)` | odd-low → six-even-right → even-seven → odd-low | `(1448t+1146,1324t+1047)` | 1 |
| `j=512t+191` | `(1024t+385,1536t+580)` | even-affine → odd-low → even-seven → odd-low | `(1384t+514,1356t+503)` | 1 |

The original `j=8t+3` proof is in [Agent3's M0Mod8Three.lean](../agent3-c-bounce-inverse/M0Mod8Three.lean). The `j=16s+2` proof, including universal admission by the preceding high sieve, is in [M0Mod16Two.lean](M0Mod16Two.lean). The other nine progressions and their shared prior-sieve admission lemma are in [M0AdditionalForcedFamilies.lean](M0AdditionalForcedFamilies.lean).

## Finite scan comparison

The reproducible `FullForcedParamScan.lean` scan over `0≤j≤2000`, `0≤m≤20` reports 642 m=0 pairs admitted by the preceding high sieve and rejected by `fullForcedExcluded`. The eleven progressions above contribute 636 distinct such j-values in this finite window:

| Progression | Count in (0≤j≤2000) |
|---|---:|
| `j=8t+3` | 250 |
| `j=16s+2, s≥1` | 124 |
| `j=32t+6` | 63 |
| `j=64t+58` | 31 |
| `j=32t+21` | 62 |
| `j=32t+15` | 63 |
| `j=128t+71` | 16 |
| `j=128t+5, t≥1` | 15 |
| `j=512t+357` | 4 |
| `j=512t+406` | 4 |
| `j=512t+191` | 4 |
| **Total** | **636** |

The remaining six finite-scan candidates are
`j ∈ {534, 581, 1046, 1093, 1159, 1343}`.
The updated [FullForcedParamScanM1M2.lean](FullForcedParamScanM1M2.lean) diagnostic computes these as the exact residual of the finite candidate list after removing the eleven progressions, and also emits terminal states for symbolic path inspection. The finite scan is discovery evidence; the universal claims come from the Lean source theorems after CI verification.

## CI dependency correction

The exact gate `sixEvenRightGate` is defined in namespace `BB6.Agent46` by `EvenRightSixOrbit.lean`. Earlier M0 proof modules had incorrectly qualified it as `BB6.Agent3.sixEvenRightGate`. The source files now use `BB6.Agent46.sixEvenRightGate`. M0Mod8Three also explicitly normalizes its target coordinates before transferring its affine-normalizer and Boolean-filter results. The phase workflow emits the fast dyadic/late-gate dependency oleans before the C58 Boolean wrapper. The next run checks all eleven progressions and the six-point residual scan.
