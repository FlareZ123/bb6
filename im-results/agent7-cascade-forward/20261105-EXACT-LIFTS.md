# Unique three-adic fatal-index lifts and exact valuations

Agent 7, 2026-11-05. This is a proved **intermediate result** for the source-indexed #746 fatal reset heights; it is not a halting decision, original-machine upper bound, or independently audited academic novelty.

## Mathematical statement

Set \(F(n)=4\cdot2^n-n-4\), \(Z(n)=2F(n)+5=8\cdot 2^n-2n-3\) (for \(n\ge4\)). For every \(k\ge0\) and \(n\ge4\) with \(3^k\mid Z(n)\), and every \(j\in\{0,1,2\}\), the theorem `fatal_shift_exact` proves the exact equivalence

\[
3^{k+1}\mid Z(n+2\cdot3^k j)
\quad\Longleftrightarrow\quad
j\equiv Z(n)/3^k\pmod3.
\]

In particular, **exactly one** of three candidate shifts passes the next divisibility level; the other two fail it, while all three retain divisibility by \(3^k\). The witness is explicit and unique, unlike an existential lifting argument.

For \(k\ge1\), if \(3^{k+1}\mid Z(n)\) then \(Z(n+2\cdot3^k)\) has **exact** \(3\)-adic valuation \(k\); the shift preserves \(n\bmod6\).

Composing this with Agent7's previously source-proved arbitrarily high valuation theorem produces `fatal_exact_valuation_four` and `fatal_exact_valuation_five`: for any bound \(N\) and any \(k\ge1\), there exists \(n>N\) in each respective class \(n\bmod6\in\{4,5\}\) for which \(3^k\mid Z(n)\) and \(3^{k+1}\nmid Z(n)\).

## Mechanism and proof

The prior \(4^{3^k}\equiv1\pmod {3^{k+1}}\) lemma yields the exact natural-number balance

\[
Z(n+2\cdot3^k j)+4\cdot3^k j
=
Z(n)+3^{k+1}m(8\cdot2^n)
\]

for an integer \(m\ge0\). Dividing by \(3^k\) is exact because the hypothesis gives divisibility of both numerators. Reduction modulo three leaves the coefficient \(4j\equiv j\). This determines the unique next digit. The exact-valuation construction chooses the nonmatching shift \(j=1\) from a high-valuation seed, preserving the surviving \(\bmod6\) index sector.

The proof uses the original source-indexed fatal-height arithmetic and the earlier all-natural high-valuation result, so it is uniform in \(n,k\). It does not claim any actual incoming parent reaches a fatal height along the blank-derived orbit.

## Verification and reproducibility

- New Lean source: [FatalValuationExact.lean](FatalValuationExact.lean).
- Dependencies: [FatalValuationPower.lean](FatalValuationPower.lean), [FatalValuationUnbounded.lean](FatalValuationUnbounded.lean), [FatalValuationBeyond.lean](FatalValuationBeyond.lean), and all their checked-in source interfaces.
- Manual Lean 4.36.0-rc2 [GitHub Actions run 42050033311](https://github.com/FlareZ123/bb6/actions/runs/42050033311): **SUCCESS** for the unchanged checked-in dependency chain, including the eight new theorem audits. Workflow head: `fea4e8ed5e6e4dfb58b03d0972ccf791f3af7e68`.
- `#print axioms` for the final `fatal_exact_valuation_four` and `fatal_exact_valuation_five` showed `[propext, Classical.choice, Quot.sound]`; the shift balance and divisibility preservation showed `[propext, Quot.sound]`. There were no `sorryAx` dependencies.

## Existing work and limitations

Earlier Agent7 [FatalValuationUnbounded.lean](FatalValuationUnbounded.lean) supplied a (nonstrict, unspecified digit) one-of-three lift and unbounded valuations. This result refines that specific mechanism to **an exact unique digit** and shows that every **exact positive finite valuation** is realized arbitrarily far out in each surviving class. Agent44's independent [source-checked unbounded inverse fan-in](../agent44-746-fanin/README.md) already establishes that candidate fatal heights can have arbitrarily many genuine synthetic first-reset parents; this new valuation result is complementary and should not be misrepresented as a new fan-in theorem. Agent44's proposed [exact odd-parent count](../agent44-746-fanin/ExactCount.md) is presently only a paper-derived and empirically audited formula.

Actual original blank-machine halting still requires reaching at least one of infinitely many \(F(n)\) with \(n\ge2049\) and \(n\bmod6\in\{4,5\}\), via the separately certified original Cryptids source bridge. No such root reachability decision follows from the lifting arithmetic.
