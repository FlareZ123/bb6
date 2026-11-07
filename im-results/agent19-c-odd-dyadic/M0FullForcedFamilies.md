# m=0 full-forced infinite families

Status: formal Lean modules are committed; the corrected original-source CI audit is pending in [run 42401719081](https://github.com/FlareZ123/bb6/actions/runs/42401719081). Treat the source-level claims as provisional until that run completes and the final axiom reports contain no `sorryAx`.

All targets below are the exact m=0 high stopping targets
`(2*j+3, 4*(j+3)-(j+5)) = (2*j+3,3*j+7)`.
The four-sector normalizer uses the source gates in this order: odd-low, even-seven, even-affine, six-even-right. Every listed terminal pair has odd right coordinate at least 5 and coordinate sum congruent to 1 or 2 modulo 4, so the source theorem `fullForcedExcluded_sound` rules out every blank-derived section hit.

| Parameter progression | Exact target | Forced inverse path | Terminal pair | Terminal sum mod 4 |
|---|---|---|---|---:|
| `j=8t+3` | `(16t+9,24t+16)` | even-affine | `(40t+23,12t+7)` | 2 |
| `j=16s+2, s≥1` | `(32s+7,48s+13)` | odd-low | `(40s+8,44s+9)` | 1 |
| `j=32t+6` | `(64t+15,96t+25)` | odd-low → six-even-right | `(168t+36,44t+9)` | 1 |
| `j=64t+58` | `(128t+119,192t+181)` | odd-low → even-seven | `(168t+153,172t+157)` | 2 |
| `j=32t+21` | `(64t+45,96t+70)` | six-even-right → six-even-right → even-affine | `(232t+159,12t+7)` | 2 |
| `j=32t+15` | `(64t+33,96t+52)` | even-affine → odd-low | `(104t+52,76t+37)` | 1 |
| `j=128t+71` | `(256t+145,384t+220)` | even-affine → odd-low → six-even-right → six-even-right | `(872t+484,76t+41)` | 1 |

The original `j=8t+3` proof is in [Agent3's M0Mod8Three.lean](../agent3-c-bounce-inverse/M0Mod8Three.lean). The `j=16s+2` proof, including universal admission by the preceding high sieve, is in [M0Mod16Two.lean](M0Mod16Two.lean). The other five progressions and their shared prior-sieve admission lemma are in [M0AdditionalForcedFamilies.lean](M0AdditionalForcedFamilies.lean).

## Finite scan comparison

The reproducible `FullForcedParamScan.lean` scan over `0≤j≤2000`, `0≤m≤20` reports 642 m=0 pairs admitted by the preceding high sieve and rejected by `fullForcedExcluded`. The seven progressions above contribute 609 distinct such j-values in this finite window:

| Progression | Count in (0≤j≤2000) |
|---|---:|
| `j=8t+3` | 250 |
| `j=16s+2, s≥1` | 124 |
| `j=32t+6` | 63 |
| `j=64t+58` | 31 |
| `j=32t+21` | 62 |
| `j=32t+15` | 63 |
| `j=128t+71` | 16 |
| **Total** | **609** |

The remaining 33 finite-scan candidates occur in residues (jmod16in{5,6,7,15}). They are not covered by these seven simple progressions and remain a target for symbolic path analysis. The scan is discovery evidence only; the universal theorems are the Lean source modules, once their CI audit passes.

## CI dependency correction

The exact gate `sixEvenRightGate` is defined in namespace `BB6.Agent46` by `EvenRightSixOrbit.lean`. The earlier M0 proof modules had incorrectly qualified it as `BB6.Agent3.sixEvenRightGate`. The source files now use `BB6.Agent46.sixEvenRightGate`; the phase workflow also emits the fast dyadic/late-gate dependency oleans before the C58 Boolean wrapper. Run 42401719081 checks the corrected dependency chain and the new M0 modules.
