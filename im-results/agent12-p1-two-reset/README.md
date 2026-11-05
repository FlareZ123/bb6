# Agent12: two-positive-reset critical P1 affine-wall obstruction

**2026-11-05; intermediate formal mathematical investigation.** This is about the original six-state P1 machine's *normalized odd inverse grammar*, not a proof of machine-wide nonhalting or BB(6). It sharpens Agent28's proposed [n>=70 draft](../agent28-p1-word-automaton/TWO-RESET-CANDIDATE.md).

## Main result and scope

The source-imported formal theorem `BB6.Agent12TwoReset.exact_two_reset_wall_impossible` in [TwoResetCombined.lean](TwoResetCombined.lean) excludes every **exact normalized** root inverse history of the shape

```
upper^r ; positive reset^(l) ; upper^s ;
positive reset^(ell) ; upper^u
```

for all n>=46, l>=2, ell>=2, provided the original normalized scalar inverse equations and the general wall-cost necessary inequality hold. It is universally quantified over all natural run lengths and scalar parameters, and therefore is not a bounded simulation or a residue search. It says **nothing** about any original inverse history containing three or more positive resets.

The proof first imports the established Agent28 one-reset source-independent budget `2^(r+l+s)<=24*(n+2)^3`, then proves the positive first-defect invariant in [FirstResetDefect.lean](FirstResetDefect.lean):

```
  ∃ C N,
    C <= 2*2^(r+l+s)  ∧
    0 < N <= n+(r+l+s)+1  ∧
    Fend+N = 7*2^(n-(r+l+s))*C.
```

The previously missing first-defect step is now formally derived from **exact** original normalized first-reset and final-upper equations using Agent28's proved source-coefficient identities and dyadic division. This closes the missing *scalar* precondition of [SecondResetBudget.lean](SecondResetBudget.lean).

Writing x=n+2, the elementary new bound `24*x^3<2^x` yields `r+l+s<=x`. The second reset's remainder is at most 4x, its dyadic weight at most 4x, and its final positive remainder and suffix weight at most 6x. Consequently, after both positive resets, total weight is at most `576*x^5` and total inverse depth at most `11*x`. The source wall inequality would require

```
  6*2^n <= 20160*(n+2)^6,
```

contradicting the fully checked all-n>=46 estimate in [TwoResetPolynomial.lean](TwoResetPolynomial.lean). The proof uses induction over n and exact natural arithmetic; it does not extrapolate from finite checks.

## Trust boundaries

- **Normalization and source identity proof:** `TwoResetCombined.lean` is a universal theorem for the exact scalar root/upper/reset/upper/reset/upper equations. The general source provenance for these equations is Agent28's `OneResetSourceBridge.lean`, `OneResetSourceEq.lean`, `OddWordSourceBridge.lean`, and `OneResetCount.lean`. At the time of writing, a further theorem quantifying directly over every genuine original `CountCone` history with exactly two positive resets has **not** been checked. That remains a precise bridging task.
- **CI:** [manual original-dependency Lean 4.36.0-rc2 workflow](../../.github/workflows/agent12-p1-two-reset.yml); first subcertificate [passed 42078427645](https://github.com/FlareZ123/bb6/actions/runs/42078427645) against untouched real Agent28 `OneResetTwoAdic` and `DefectTransport`. Check the latest workflow for the complete composed theorem. The independent local proof was initially compiled against signature-matched temporary axioms, which do not appear in the repository artifacts; only actual original-dependency CI provides proof provenance.
- **Prior art:** The prior n>=70 proposal already described a two-reset polynomial strategy. The sharper n>=46 bound, positive-first-defect construction, and end-to-end normalized composition are the specific contribution. Independent novelty review against external literature remains pending.
- **Unsolved:** Critical inverse histories with at least three positive resets, exceptional c=1 and even exits, authentic blank-root nonhalting, and a universal BB(6) upper bound all remain open.

## Next decisive action

Prove `source_critical_wall_needs_three_resets` by extending Agent28's genuine `CountCone` history decomposition with an exact-two-reset case, deriving normalized scalar equations from `UpperTail` and `inverseAt_iff_power_mass`, and invoking the composed theorem with Agent28's source all-word wall inequality. This is the actual source-quantifier bridge. Then investigate three and more resets instead of multiplying finite exclusions.
