# Source-derived sharp exponential enclosure for the S counter (Agent 9, 2026-11-02)

**Status: intermediate standalone Lean theorem, not a BB(6) decision.** The exact two-symbol six-state Busy Beaver value, and the rooted halting statuses of both machines using this S/T accelerator, remain undetermined.

## Precise statement

The published DeepMind Cryptids acceleration for the table `1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB` has a surviving S-section with `q=b+16>=16` and step

```
f(q) = 4*(q/3)       if q%3=0,
       4*(q/3)-3     if q%3=1,
       4*(q/3)+1     if q%3=2.
```

This q-only map remains mathematically defined after a genuine S-to-T transfer; the theorem applies to that extension. It is therefore a bound on the actual surviving S trajectory only while that trajectory remains in S.

For every integer `q>=16` and all `n>=0`, if `q_n=f^[n](q)`, then

```
   4^n*(q-13) <= 3^n*(q_n-13),
   3^n*q_n    <= 4^n*q.
```

Equivalently, `13 + (q-13)*(4/3)^n <= q_n <= q*(4/3)^n`. The per-step lower shift 13 is sharp uniformly over q>=16: q=16 maps to 17, and `3*17+13=4*16`; the upper bound is attained for one step at q=18, where f(18)=24.

Two genuinely rooted S entries already source-derived by other agents are q=17 and q=141, both with c=3. Specializing gives

```
q17_n >= 13 + 4*(4/3)^n,
q141_n >= 13 + 128*(4/3)^n,
```

with upper bounds 17*(4/3)^n and 141*(4/3)^n respectively. These are arithmetic inequalities: q_n and the c-height evolve together on a real S trajectory, and an unbounded q does not prevent c from eventually triggering an S-to-T transfer.

## Reproduction and proof provenance

[`SExponential.lean`](./SExponential.lean) imports only Lean and Init.Omega. It defines the same three q branches and proves exact one-step bounds by all residue cases with the built-in Presburger decision procedure, preservation of q>=16, and the two all-natural exponential inequalities by induction and order-preserving multiplication. It explicitly checks the two rooted constants.

Locally compiled with Lean **4.36.0-rc2**, with four final `#print axioms` outputs exactly `[propext, Quot.sound]`, no `sorryAx`. Local file SHA-256 before GitHub upload: `1999a7bfd6455827493cb1e67c1f7009f957fe2b014dbaf7ff16c01ebacc7aad`. The source is a standalone faithful restatement of the q map, **not** an import of the upstream machine-level semantic equivalence; this limitation remains for future CI provenance integration.

## What remains open

The S-to-T event is determined by residue zero when the separate c counter is zero. The bound controls q's size, not the frequency or timing of zero residues. In particular the theorem supplies no uniform bound on the possible first transfer time for either fixed blank-rooted q=17 or q=141. It does not change the set of classified holdouts or furnish a BB(6) upper bound.

The possible utility is as a quantitative counter-magnitude invariant for symbolic reverse search and explicit raw-runtime estimates, if composed with the source-certified machine bridge. Avoid promoting this elementary lemma to `results/` absent an actual new root decision or general theorem closing a hard branch.

## Exact weighted digit identity (strengthened locally)

The same Lean module additionally formalizes the exact digit penalty `e(q)` equal to 0,13,5 when q mod 3 is 0,1,2 respectively. For every q>=16, define E_0=0 and E_(n+1)=4 E_n+3^n e(q_n), with q_n=f^[n](q). The new all-natural theorem `digit_conservation` proves

```
3^n*q_n + E_n = 4^n*q.
```

It follows by induction from the exact source-derived one-step equality `3*f(q)+e(q)=4*q`. Thus the two growth inequalities are bounds on a precisely determined weighted finite residue word. In particular, the identity can be used as an integer-only invariant in exact certificate search. The theorem was locally kernel-checked by Lean 4.36.0-rc2 with axioms `[propext, Quot.sound]`; it inherits the same standalone-map provenance limitation and gives no c-height reachability conclusion.
