# Finite dyadic word feasibility vs. recursive modular-cone exclusion

**Status: exact finite-level computational agreement and a mathematical induction program, NOT an accepted all-depth theorem.** This is a candidate useful bridge between Agent21's density-zero word extinction proof and Agent42's already-source-certified finite modular-cone exclusion program. Do not move this to `results/` or advertise asymptotic completeness until the induction is checked.

## Proposed all-precision identity

For a signed pair `p=(x,y)`, define `s=-x-2*y` and `z=(-x-2-(s%2))/2`. The candidate identity is

```lean
BB6.Agent42ModularCone.excluded b p = true ↔
  ¬ BB6.Agent21Dyadic.OpenAt s z b
```

for every natural precision `b`. The source-independent `OpenAt` is defined in `DyadicReach.lean` by a completed positive-gap word of total cost `b`, or a pending word of total cost `b+1` whose final gap is at least 2; the numerator must vanish modulo `2^b`. The executable `excluded` is in `im-results/agent42-modular-cone/ModularCone.lean` and its integer recurrence is mirrored by `probe.py`.

Independent JavaScript implementations of those two definitions agreed **as exact complements on every canonical pair `0≤x,y<2^b` for b=2,3,4,5,6**, comprising respectively 16,64,256,1024,4096 pairs; mismatches: 0 at each precision. Also every `j=0..255` for each of four high-stop rays `m=0,1,2,3` agreed at b=8. The complete b=6 counts are 2174 excluded/closed and 1922 admitted/open; b=5 counts 495 excluded/closed and 529 admitted/open. This is finite computational evidence only. No implication for arbitrary b is yet certified.

## Why the identity is plausible: exact first-letter arithmetic

Set `Q=x+y+((x+y)%2)`. With `s,z` as above and any positive first gap `r`,

```
z + offset(s,r) = -x-y - ((-x+3*r+1)%2).
```

If `2^b` divides the compatible-word numerator and `0<r≤b`, then `2^r` divides this one-gap numerator. Its evenness forces

```
r%2=(y+1)%2,
z+offset(s,r)=-Q,
2^r | Q.
```

A source-independent Lean formalization of these facts is in `DyadicGapConstraint.lean` (compilation pending). If `v=v₂(Q)<b`, then necessarily `r≤v<b`. Thus the only possible leading letters are:

- `r=1`, possible exactly if `y` is even; its signed parent is Agent42's `direct` pair, consuming one bit.
- `r=n+2≤v`, where `n%2=(x+1+((x+y)%2))%2`; its signed parent is Agent42's `high n` pair, consuming `n+2` bits.

In either case, exact signed arithmetic gives `s_child=s+shift r` and `2^r*z_child=z+offset(s,r)`. Removing the first gap from a completed or pending word should therefore correspond to the recursive `check` child. The `HighValid` side condition is forced when `n+2≤v` and the parity condition holds: `Q/2^(n+1)` is even, so the computed high-parent right numerator is even. In the base case `2^b|Q`, the single gap `r=b` (or pending `r=b+1` when parity changes) supplies `OpenAt`. The immediate `Bad` cases have `v=1`, odd `y`, and no possible first gap, so `OpenAt` fails.

## Formal proof dependencies still missing

1. Prove `OpenAt` is invariant under `x,y` reduction modulo `2^b`. Although `S` alone needs b+1 bits, its dependence on x cancels with Z. For any nonempty positive word, its coefficient is odd, and changing `x` and `y` by `2^b*u` and `2^b*v` changes `z+acc(s,w)` by
   `-2^(b-1)*(u*(1+coeff(w))+2*v*coeff(w))`, a multiple of `2^b`.
2. Prove **fuel saturation** `check f b s=check b b s` when `f≥b`. Every direct/high inverse edge consumes at least one precision bit; extra fuel is irrelevant.
3. Derive the signed parent equations and `HighValid` automatic-validity lemma from the original `q,valuation,Allowed` formulas; preserve the pending-word case on stripping/prepending.
4. Induct on `b` using the exact first-gap classification to compare `OpenAt` to the disjunction of open recursive children. The Boolean `check` is the complement of that disjunction.

## Potential actual mathematical payoff

Agent21's **original-source certified** uniform affine sparse cover (CI [46102569750](https://github.com/FlareZ123/bb6/actions/runs/46102569750)) bounds the fraction of `OpenAt` residues on every admissible affine ray by `1/d` at a common precision, for arbitrary `d>0`. If the one-sided implication `¬OpenAt → excluded=true` can be proved uniformly, the existing executable Agent42 checker would provably certify an arbitrarily large fraction `1-1/d` of all high-right targets on **every** such ray, at one common precision. This is a meaningful *asymptotic coverage/completeness theorem for a concrete all-time exclusion algorithm*; it is not a nonhalting proof for a particular Machine C source or a BB(6) upper bound.

**Scope caution:** Density-zero of *actually reached halting parameter pairs* is already forced by deterministic first-halt uniqueness, so it is not the payoff of this proposed bridge. The useful statement is about all nonterminal target residues and the certificate algorithm.
