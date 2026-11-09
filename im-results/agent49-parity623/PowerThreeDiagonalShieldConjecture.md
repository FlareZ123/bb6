# A power-of-three diagonal shield suggested by complete #623 fatal spectra

**Agent 49, 9 November 2026. Status: finite computational conjecture.** The following proposed infinite exclusions are **NOT proved**, have not received a Lean audit, and do not establish nonhalting of the authentic blank-root orbit. They provide a sharply defined next inductive proof target derived from the all-parameter source-certified fatal-set recurrence in [FullFailureSpectrum.md](FullFailureSpectrum.md).

Let `E_b={a∈ℕ : drainB(a,b,d)=none}`, independent of d. The complete original-source recurrences are

```text
E_0={}
E_(3q)= {x-1 : x∈E_(q-1), x>0} (q>0)
E_(3q+1)= {0} ∪ (E_q+1)
E_(3q+2)= ({0} if 0∈E_q else {}) ∪ (E_(q+1)+1).
```

## New explicit candidate invariant

For each integer `p≥1`, propose

```text
(a,b even and a+b=3^p-1)  ==> a not in E_b
(a,b even and a+b=3^p-3)  ==> a not in E_b.
```

These are **two entire finite anti-diagonals of the exact fatal relation**, not ordinary finite prefixes in b for a fixed a. The precise tested range was p=1..9 inclusive. For each p, all even `b` between zero and the corresponding sum (and `a=sum-b`) were enumerated by the exact recursive E_b formula; **zero counterexamples** occurred. This does not prove p≥10. The family sizes grow exponentially with p, and the test itself can be reproduced using:

```python
from functools import cache

@cache
def E(b):
    if b == 0: return ()
    q, r = divmod(b, 3)
    if r == 0:
        return tuple(x-1 for x in E(q-1) if x > 0)
    if r == 1:
        return (0,) + tuple(x+1 for x in E(q))
    return ((0,) if 0 in E(q) else ()) + tuple(x+1 for x in E(q+1))

for p in range(1, 10):
    for s in (3**p-3, 3**p-1):
        assert all((s-b) not in E(b) for b in range(0, s+1, 2))
```

Additional finite pattern, checked for p=1..9: `E_(3^p-2)={0}` and `E_(3^p)=∅` for odd p; `E_(3^p-2)={0,2}` and `E_(3^p)={0}` for even p. This pattern itself is a separate, simpler candidate for proof by the exact ternary recurrence.

## Conditional authentic-map consequence

For every **even first counter** `a=3^p±1>0` and every odd third counter `d`, the source-certified [ExactOddSectorSource.lean](ExactOddSectorSource.lean) says terminality occurs only in one of two sectors:

- Far-left `a≥d+5`, with `b=d+3` even, `x=a-d-5` even. Then `x+b=a-2`, equal to `3^p-3` for `a=3^p-1` or `3^p-1` for `a=3^p+1`. The candidate diagonal shield would exclude this branch.
- Near-right `a≤d+3`, with `b=a-1` even, `x=d+4-a` odd. The observed exact E_(3^p-2) and E_(3^p) consist only of even values and would exclude this branch.

If BOTH infinite conjectures are proved, the resulting **infinite vertical family** `T(D(3^p-1,d))≠none` and `T(D(3^p+1,d))≠none` for every odd `d` follows formally. This would establish a root-relevant all-time one-step safety family, though **not** a global root invariant or BB(6) solution.

The next research task is a simultaneous induction for the pair of diagonal anti-membership statements under ternary changes `3q+r`. Check the two parity-dependent small terminal spectra in the same induction. If this fails, produce an explicit first counterexample rather than extending finite horizons without theory. Avoid adding any conjecture to `results/`.

## Elementary infinite sublemma: the special boundary spectra are derivable

The auxiliary pattern above **does admit an all-p paper induction** from the already source-certified exact recurrence (its standalone Lean proof is not included here). Put `A_p=E_(3^p)` and `B_p=E_(3^p-1)`. For p≥1 the source recurrence gives

```text
A_p = down(B_(p-1))
B_p = ({0} if 0 in B_(p-1) else {}) union (A_(p-1)+1).
```

With `A_0=E_1={0}` and `B_0=E_0=∅`, induction yields `A_p={0}, B_p=∅` for p positive even and `A_p=∅, B_p={1}` for p odd. Also `E_(3^p-2)={0}∪(B_(p-1)+1)`, so `E_(3^p-2)={0,2}` for even p and `{0}` for odd p. **This settles the previously empirical near-right parity component on paper for every p.** The full infinite anti-diagonal shield remains an explicitly unproved conjecture and is the only remaining missing ingredient for the proposed entire safe-column conclusion.
