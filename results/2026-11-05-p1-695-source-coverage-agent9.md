# Source-certified P1 critical-gateway exclusion density: at least 695/1024

**Agent 9, 2026-11-05.** A combined asymptotic theorem from explicitly listed genuine original-source P1 blank-reachability exclusions. This is a mathematical restriction on possible halting-critical resets for one six-state holdout. The machine's halting status and BB(6) remain unresolved.

## Statement

For the original P1 accelerated blank-start reachability relation `BB6.Agent1.Reach`, define

```text
H(n) = 14*2^n - 2*n - 10
E = { q≥1 : ¬ BB6.Agent1.Reach 2 (H(16*q+2)) }.
```

The original-source proven theorems cited below imply

```text
liminf_{X→∞} |E ∩ {1,...,X}| / X ≥ 695/1024
                                  = 67.87109375%.
```

Proof: The source-certified conditions partition into disjoint sets of residue classes for q modulo 1024. The separate low-residue conditions have finite initial exceptions only, irrelevant to lower asymptotic density.

| Disjoint condition on q | Count of q residues mod 1024 | Source-level justification |
|---|---:|---|
| `q%4∈{0,3}` | 512 | Agent1's original-source whole-sector exclusion, [theorem synthesis](./2026-11-02-p1-entire-2-and-50-mod64-exclusions.md) |
| `q%256∈{14,30,57,61,73,77,106,138,173,217,218,221,233,238,250,254}` | 64 | Agent50's three and Agent8's thirteen, [Agent8 source CI 42110442046](https://github.com/FlareZ123/bb6/actions/runs/42110442046) |
| `q%1024∈{29,297}` | 2 | Source CI [42072169186](https://github.com/FlareZ123/bb6/actions/runs/42072169186), [42108190498](https://github.com/FlareZ123/bb6/actions/runs/42108190498) |
| Previous Agent8 cost-11 list of 31 `q mod1024` residues | 31 | [Original-source CI 42113422986](https://github.com/FlareZ123/bb6/actions/runs/42113422986), [source list](../im-results/agent8-p1-shadow-cost11-batch/README.md) |
| New Agent9 cost-10 list of 49 `q mod1024` residues | 49 | [q185 source CI 42114293669](https://github.com/FlareZ123/bb6/actions/runs/42114293669), [remaining 48 original-source CI 42115932188](https://github.com/FlareZ123/bb6/actions/runs/42115932188), [49-family proof](./2026-11-05-p1-49-mod16384-blank-gateway-agent9.md) |
| New Agent9 cost-11 list of 34 `q mod1024` residues | 34 | [Both successful jobs, original-source CI 42116576249](https://github.com/FlareZ123/bb6/actions/runs/42116576249), [reproducible generator](../im-results/agent9-p1-q1024-cost11/generate11.py) |
| New Agent9 three `q mod1024∈{1,6,26}` tails, for q≥1024 | 3 | [Source CI 42117327610](https://github.com/FlareZ123/bb6/actions/runs/42117327610), [reproducible generator](../im-results/agent9-p1-q1024-low/generate_low.py) |
| **Total** | **695** | All seven contributions are disjoint |

For low q residue representatives, the exact source theorem is parametrized by `q=1025+1024r`, `q=1030+1024r`, or `q=1050+1024r` for `r≥0`. It is therefore **not** a theorem about the specific small indices `q=1,6,26`. Removing at most three finite exceptions does not change the asymptotic density.

The finite disjoint count is checked by an independently compiled Lean 4.36.0-rc2 closed computation in [DensityCount695.lean](../im-results/agent9-p1-q1024-cost11/DensityCount695.lean), theorem `BB6.Agent9Density.certified_density_695`; its `#print axioms` reports **no axioms**. The file precisely enumerates all underlying residues. The derivation of the asymptotic inequality additionally uses elementary periodicity and each separately original-source compiled reachability theorem. There is not currently a single Lean file importing every original Reach exclusion and proving the analytic liminf bound.

## New mathematical mechanism, scope and traceability

The two feeder roots of a necessary P1 critical reset are projected through an **original-source-certified dyadic shadow inverse** into integer graph coordinates `(m,z)`. Every real odd inverse branch must satisfy the exact integer transition

```text
z=2^t*v,
2*z'+1=16*q+h+m+t+v,
(m',z')=(m+t+1,z'),
h=8 or 9 (the two source-authentic feeders).
```

For each new residue `q=q0+1024r`, every two-feeder graph is closed on an explicit finite list of affine nodes `(m,z0+a*r)`. Each original-source Lean kernel proof establishes exact closure, m≤10 or m≤11, and `256∤z` at every graph state for all natural r. The imported reusable original-source theorem then handles **all** genuine predecessor types, including exceptional `c=1`, left-mod-four branches, positive even-right source leaves and the complete two-feeder critical-root equivalence. No finite simulation cutoff or independent mock reachability model is used.

The new source method is a reproducible proof generator emitting ordinary explicit Lean proof terms, independently kernel-checked and not trusted for semantic correctness. Each theorem is a quantified all-time necessary-gateway exclusion, established against original machine definitions by source audits. [Generic original-source core](../im-results/agent8-p1-shadow-cylinder/GenericCritical.lean), [cost11 extension](../im-results/agent8-p1-shadow-cost11/GenericCritical11.lean), and [Agent9 generator](../im-results/agent9-p1-q1024-batch/generate.py) are auditable.

## Precise limitations

The density concerns **necessary gateway indices for one machine** and is not the frequency of nonhalting six-state Turing machines, not the fraction of all possible machine behaviors decided, not a bound on run time, and not an upper or exact value for BB(6). The uncovered residue classes and other halting gate sectors remain mathematically live.

This synthesis is a **strict improvement on the previously documented conservative 578/1024 bound** in [Agent8's report](./2026-11-05-p1-thirteen-period256-source-lift.md). Further genuine-source certificates may supersede the stated numerical threshold; treat this as a dated reproducible lower bound, not an upper bound on what could ever be excluded. External prior-art comparison has not been exhaustively performed.
