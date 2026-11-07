# Space Needle terminal-feeder and root analysis

**Status (2026-11-07): BB(6) remains unresolved.** The Space Needle machine has not been proved nonhalting from its blank-root state. The work below narrows the terminal-feeder problem and records strong finite computational evidence, while preserving the distinction between feeder impossibility and root nonreachability.

## 1. Existing source-level reduction

The source-checked Space Needle development is based on the original high-level transition function and includes the terminal-predecessor identity

[
2^{k+2}+3=(2^{v+1}+3)(2q+3)+2v.
]

The existing fifth-root and cubic-parent work reduces a halting question to reachability of a finite family of synthetic feeder states for each fixed terminal exponent. Relevant source files and workflows are linked from [the research board](../../../research/BOARD.md). The earlier original-source checks are recorded in [CI run 42355480381](https://github.com/FlareZ123/bb6/actions/runs/42355480381).

The local formalization starts at high-level state `N 1`, with counter (d=1). Its shifted variable is (b=d+2), initially 3. The first high-level transition sends (d=1) to (d=4), hence (b=6).

## 2. Modular feeder exclusions

The file [`SpaceNeedleObstructionFamilies.lean`](SpaceNeedleObstructionFamilies.lean) now exposes a general necessary modular identity:

[
mmid 2^{v+1}+3
quadLongrightarrowquad
(2^{k+2}+3)mod m=(2v)mod m
]

for every terminal feeder. The theorem `no_terminal_by_modular_residue_avoidance` turns absence of the required residue from the powers-of-two residues into a feeder exclusion. A periodic lift proves whole arithmetic progressions.

### Formalized infinite progressions

| Modulus | Excluded valuation classes |
|---:|---|
| 5 | (vequiv4pmod{20}) (existing) |
| 7 | (vequiv1,4,10,19pmod{21}) |
| 11 | (vequiv62pmod{110}) |
| 13 | (vequiv21pmod{156}) |
| 19 | (vequiv201pmod{342}) |
| 29 | (vequiv74pmod{812}) |
| 79 | (vequiv9,48pmod{3081}) |
| 103 | (vequiv59pmod{5253}) |

The union of these 12 progressions has computed natural density

[
rac{570208311809}{2288864948370}
approx 0.2491227419.
]

This is an exact generalized-CRT inclusion-exclusion calculation for the listed progressions. It is not a frequency statement about the actual orbit.

### Composite CRT obstructions

The same file now proves that no terminal feeder exists at the fixed valuations (v=7) and (v=12). In each case, every relevant prime factor separately admits a power-of-two residue, but the required exponent congruences conflict. These two formal proofs address omissions in an external hard-coded CRT reference list.

[CI run 42357543053](https://github.com/FlareZ123/bb6/actions/runs/42357543053) successfully checked the periodic progression development. [CI run 42358417424](https://github.com/FlareZ123/bb6/actions/runs/42358417424) checks the modular identity and composite CRT additions; its status was pending at the time of this update.

## 3. Search infrastructure

[`find_modular_progressions.py`](find_modular_progressions.py) enumerates prime-modulus CRT progressions. With the default prime limit 103, it finds 157 candidate progressions. Only a subset is currently formalized in Lean. The script is a discovery tool, not a proof certificate for every emitted row.

## 4. External 100-million-update trajectory

The external repository [`oohzaim1-afk/space-needle-100M`](https://github.com/oohzaim1-afk/space-needle-100M), inspected at commit `96e50a6ad829fa43e4ecfdf881b6679e599ef0b4`, reports 100,000,000 exact-integer updates from (b_0=6), with no power-of-two term. Its final term has 94,125,050 bits. The report includes 400 checkpoints and independent C+GMP, Rust, Python-prefix, and block-affine cross-checks.

The detailed source and indexing audit is in [`resources/2026-11-07-space-needle-100m.md`](../../../resources/2026-11-07-space-needle-100m.md). This finite computation is strong evidence and a reason to avoid duplicating the same forward prefix. It is not a proof of nonhalting.

## 5. Audit of the external CRT classification

The separate [CRT audit note](../../../resources/2026-11-07-space-needle-crt-audit.md) records that the external `crt_obstruction.py` hard-coded 17-value reference list for (1le ale40) is inconsistent with its own factor/order/discrete-log/CRT algorithm. Independent recomputation yields 23 obstructions, adding (a=7,12,18,28,35,36). The Lean file now proves the (a=7,12) cases; (a=18,28,35,36) remain computational CRT certificates. The external 96/120 summary has not been independently rechecked and remains unverified.

## 6. Main unresolved problem

All results above concern whether a synthetic state can be an immediate terminal feeder. The central missing theorem is still:

**Prove that the blank-root Space Needle trajectory cannot reach any terminal feeder that survives the modular restrictions.**

The highest-value next work is to integrate the modular valuation filters with the existing `NeedleRootCubic` and exact root-decision machinery, and to develop a parameter-uniform root-reachability obstruction. Repeating the same finite forward simulation is lower priority given the external 100-million-update evidence.
