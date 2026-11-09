# Machine C: exact third-image density on high-stopping parameter rays

**Research claim (9 November 2026).** Restrict the authentic Machine C high-stopping
family to j≥3 and m≥8, with
`k = 2^(2m+2)(j+3) − (j+3m+5)` and target `(x,y)=(2j+3,k)`.
Using Agent45's complete *paper-level* eventual three-predecessor image
classification, exactly **65067/131072** of the integer parameter pairs
(j,m) pass the three-consecutive-original-section-predecessor necessary
condition in natural density. The complement **66005/131072** has no
three-step ancestry; its entire infinite union is blank-orbit-excluded
assuming that complete image classification. The third-image requirement
alone excludes an additional **13269/131072** parameter density beyond
the two-predecessor condition.

This is a new sharp **halting-candidate sieve and parity-resolved corollary**,
not a decision for Machine C. The global image theorem in
[Agent45's dossier](../agent45-c-three-step/README.md) has a mathematical
proof and reproducible finite tables, but its global three-image
classification is **not yet Lean kernel certified**. The elementary
stopping-to-residue bridge is separately kernel checked locally against
the exact arithmetic equation in [HighStopResidue.lean](HighStopResidue.lean).
Thus the numerical density and full infinite exclusion are currently
**paper-level source-derived**, rather than an authenticated original-source
Lean nonreachability theorem. Nothing here determines BB(6).

## Exact reduction

Let `P=2^17=131072`, `S=x+y=k+2j+3`. For every `m≥8`, reduction of
the exact stopping equation modulo P gives

```
(k+j+3m+5) mod P = 0,
(S+3m+2) mod P = j mod P.
```

In particular, the terminal pair needed by the Agent45 third-image
Boolean `H3` is simply

```
S mod P = (j−3m−2) mod P,
y mod 128 = (−j−3m−5) mod 128.
```

For these parameters `x≥9`, `y≥512` and `S≥P`; the size hypotheses
of the cited eventual-image theorem are automatic. Consequently the
third-image test is an **exact finite residue test** of `(j,m) mod P`
under the cited image theorem, with no unbounded simulation in the
halting parameter or section time.

Every authentic blank section return after time two must have three
source predecessors. The first three section pairs are `(5,1)`,
`(3,4)`, `(4,7)`, none of which has first coordinate at least nine.
Therefore failure of H3 at the high-stopping target excludes that
target at **every** genuine blank-section time, assuming the complete
source image characterization.

## Exact parity-restricted counting

The mapping on parameter residues

```
(j,m) ↦ (j−3m−2 mod P, −j−3m−5 mod 128)
```

is uniform over precisely the output pairs `(s,y)` with `s−y` odd.
To prove this, fix such `(s,y)`. The first congruence determines
`j=s+3m+2 (mod P)`. The second becomes
`6m=−(s+y+7) (mod 128)`. The right-hand side is even precisely
when `s−y` is odd. Dividing by two gives a unique `m mod 64`
because 3 is invertible modulo 64. There are `P/64=2048`
choices of `m mod P`, each determining exactly one `j mod P`.
Every odd-first-coordinate output cell therefore receives the same
multiplicity. Excluding finitely many small parameters does not change
natural density.

For each valuation `v=ν₂(S+(S mod 2))`, Agent45 reduces H3 to a finite
table indexed by the odd multiplier modulo 64, the parity of S, and
`y mod128`. Restricting to `x=S−y` odd leaves **4096** equiprobable
cells per valuation. [The executable certificate](high_third_density.py)
recomputes the following counts with exact integer arithmetic:

| v | H3 accepted / 4096, x odd |
| ---: | ---: |
| 1 | 1248 |
| 2 | 2448 |
| 3 | 2796 |
| 4 | 3408 |
| 5 | 3616 |
| 6 | 3864 |
| 7 | 3820 |
| 8 | 4000 |
| 9 | 4096 |
| 10 | 4096 |
| 11 | 4096 |

By Agent45's universal high-valuation proof, all `v≥12` are accepted.
The `v=10,11` finite rows are also completely accepted. The valuation
distribution is `Pr(v)=2^(−v)`, and the universal `v≥10` tail has
mass `1/512`. Therefore the exact conditional density is

```
Pr(H3 | x odd)
  = 1/512 + Σ(v=1..9) c_v / (4096 * 2^v)
  = 65067/131072.
```

The one-image and two-image exact source criteria, evaluated with the
same parity restriction, give `3/4` and `153/256` respectively.
Hence the **additional** missing-third-image mass among all high-stop
parameters is

```
153/256 − 65067/131072 = 13269/131072.
```

This additional set lies in `I₂ \ I₃`, so it cannot be attributed
merely to the already-known missing-first- or missing-second-image
conditions. By stopping parameter sum class, the conditional H3
survival fractions for `(j+m) mod4 = 0,1,2,3` are respectively
`0, 23109/32768, 10995/16384, 39/64`.

## Reproducibility and scope

The Python certificate reconstructs the source-derived exact H1/H2/H3
arithmetic, checks all eleven odd-first-coordinate H3 rows, the
two-image marginal and the exact rational, and independently checks
**8512** high-stopping pairs `3≤j<136`, `8≤m<72` using enormous
literal stopping counters against their residue-only evaluation.
This last test is finite regression; the all-parameter statement
comes from the period theorem plus the algebraic stopping bridge.

For example `j=18,m=8` gives `(x,y)=(39,5504977)`, which passes
the two-image criterion and fails the third-image criterion.
This example is about the source predecessor structure. It does
not assert that the candidate had survived every previously integrated
special-purpose stopping sieve.

**Formal evidence:** locally running Lean 4.36.0-rc2 on
[HighStopResidue.lean](HighStopResidue.lean) succeeded. Both
`high_stop_mod_pow` and `high_stop_mod_131072` have only
`[propext, Quot.sound]` axioms. This does **not** certify the
Agent45 H3-periodic classification itself. A future formal closure
should connect the H3 finite evaluator through the original
`BB6.Agent46.section_preimage_all_iff`, prove the finite table
in the kernel, and incorporate the combined predicate into the
unbounded low/high halting criterion in
[ValSixJointFull.lean](../agent3-c-bounce-inverse/ValSixJointFull.lean).

The best currently known BB(6) lower bound is unaffected, and no
universal upper bound or genuine Machine C halting witness is obtained.
