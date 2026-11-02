# Original-source-certified M32 inverse-depth barriers for Machine C

Agent 15 (integration) with Agent 11's M32 precursor, 2026-11-02. **Intermediate research:** Machine C and BB(6) remain undecided. This note records exact verified statements and reproducibility.

## Imported original-source M32 exclusions

The 40-shard original CLine finite-quotient proof was kernel-checked in [CI 41538277695](https://github.com/FlareZ123/bb6/actions/runs/41538277695) on commit `640d616ac420281216ad5f197ab255c07982035f`. Agent11's eight-cylinder extension was kernel-checked in [CI 41544958543](https://github.com/FlareZ123/bb6/actions/runs/41544958543), commit `a41218e58b30499b9082b61e54b1975479e35963`.

The isolated source section-reachability embedding `BB6.Agent15.m32_section_reach_embeds` is in `M32SectionEmbedding.lean`, using `BB6.Agent46.section_exact` and original `BB6CLine.Reach`. It imports no M8/M16 certificate and avoids unrelated `CCert` namespace collisions.

[CI 41546973263](https://github.com/FlareZ123/bb6/actions/runs/41546973263) succeeded on commit `ad53cd2be7a7f4e7c356c946912d7e4cecdd9167`. It compiled `M32AllDepthOriginal.lean` with exact original imported sources, proving:

- `BB6.Agent11.original_m32_odd_depth_barrier`: for arbitrary `a,d,q`, if `a%4=3`, `1≤q`, `(a+2*(2^(d+1)*(2*q+1)-2))%32=23`, and `m32DepthClass d q`, then `¬ BB6.Agent15.CReach a (2^(d+1)*(2*q+1)-2)`. The predicate `m32DepthClass` contains eight depth and odd-part residue classes with `d%8` odd.
- `BB6.Agent11.original_m32_first_halt_two_classes`: if `m%2048=584` or `1864`, and `k+3*m+4=2^(2*m+3)`, then `¬ BB6.Agent3.CReach 1 k`.

## New second stopping-family theorem

The original Machine C exact second-family immediate-halting parameter equation (Agent15's already-certified `SectionParam.lean`) is

```
k+j+3*m+5 = 2^(2*m+2)*(j+3),
state=(2*j+3,k).
```

Our new `M32SecondArithmetic.lean` and `M32SecondDepth.lean`, source-verified in **[CI 41547366682](https://github.com/FlareZ123/bb6/actions/runs/41547366682)**, commit `cce4e0722bdb4efa4ad12697a82c2c4c66cb1f94`, prove the following *all-natural* implication:

```
m%16 = 11
r+3 ≤ m
q ≤ j
j+3*m+3 = 2^(2*r+2)*(2*q+1)
k+j+3*m+5 = 2^(2*m+2)*(j+3)
m32SecondParamClass r q
-------------------------------------------------
¬ BB6.Agent15.CReach (2*j+3) k
```

Here `m32SecondParamClass r q` means one of:

```
r%4=0 and q%8 in {0,3}
r%4=1 and q%8 in {2,7}
r%4=2 and q%8 in {3,4}
r%4=3 and q%8 in {6,7}.
```

The proof factors `k+2=2^(2*r+2)*(2*Q+1)` with `Q=2^(2*m-2*r-1)*(j+3)-q-1≥1`; its normalized affine inverse depth is `d=2*r+1`, and `((2*j+3)+2*k)%32=23`. Since `2^(2*m-2*r-1)` is divisible by 8, `Q%8=-q-1 (mod 8)`, placing the normalized state in one of the M32 certified unreachable cylinders. The theorem uses exactly the source-connected `original_m32_odd_depth_barrier`, independent of the earlier M8 even-depth halting exclusions.

**Nonvacuity at every odd depth:** `second_m32_original_unbounded r lower` proves `∀r,lower, ∃m,j,k,` with `lower≤m`, the *exact* second stopping equation above, and `¬CReach (2*j+3) k`. Its constructive witness sets `m=16*(r+lower)+11`, `q=8*m+2*(r%4)`, `j=2^(2*r+2)*(2*q+1)-3*m-3`, `k=2^(2*m+2)*(j+3)-j-3*m-5`. The natural subtraction guards, the Diophantine equation, and the unreachable conclusion are all proved in Lean. This establishes arbitrarily high **input candidate** indices excluded at every odd affine-inverse depth, never reachability from the genuine blank tape.

The manual workflow `.github/workflows/agent11-m32-eight-fast-check.yml` downloads *pinned artifacts* from source-certified Agent43 CI 41538277695 and recompiles original CLine, Agent46/3/15 section source and the entire proof chain. Its final `#print axioms` reports only `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. No copied theorem signatures, synthetic oracles, or arbitrary depth cutoff is used in this final source check.

**Open obligation:** the remaining infinite parameter families may contain genuine blank-origin halting inputs. Neither this result nor its prior modular exclusions decide Machine C nonhalting. Establishing BB(6) also needs exhaustive coverage of *every* 6-state candidate and a matching best lower bound. Independent novelty and significance review are needed before promotion to `results/`.
