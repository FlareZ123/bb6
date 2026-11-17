# Logarithmic upper bound on fatal B-drain first counters

**Status:** locally kernel-checked in Lean 4.36.0-rc2; source-connected adapter still needs integration in the original Cryptids import environment. This is an intermediate result, not a BB(6) solution.

## Theorem

FailureBudgetPowerBound.lean reproduces the recursive Boolean predicate badAll from im-results/agent49-parity623/FullFailureSpectrumSource.lean and proves

\[
\operatorname{badAll}(a,b)=\texttt{true}
\quad\Longrightarrow\quad
3^a\le 2b+1.
\]

Equivalently, every fatal first counter satisfies

\[
a\le \left\lfloor\log_3(2b+1)\right\rfloor.
\]

The proof is a two-sided induction on the ternary threshold
\[
\tau(k)=\frac{3^k-1}{2}.
\]
Both the strict interval \(b<\tau(k+1)\) and the boundary \(b=\tau(k+1)\) are maintained. The boundary case is essential: in the residue-two branch, the recursive block count can land exactly on the previous ternary threshold.

## Asymptotic sharpness

The file also defines
\[
b_0=1,\qquad b_{k+1}=3b_k-1
\]
and proves
\[
\operatorname{badAll}(k,b_k)=\texttt{true},
\qquad
2b_k+1=3^k+2.
\]

Thus the exponential bound is sharp up to an additive constant of 2 in infinitely many fatal pairs. In particular, the logarithmic growth rate of the largest fatal first counter cannot be improved below \(\log_3(2b)\) by more than a bounded additive term.

## Connection to the exact #623 drain

The existing source module im-results/agent49-parity623/FullFailureSpectrumSource.lean proves

\[
\operatorname{flatB}(a,b,d)=\texttt{none}
\iff
\operatorname{badAll}(a,b)=\texttt{true},
\]

and its imported FlatDrainSource proves flatB_eq_drainB, identifying flatB with the original Cryptids #623 drainB.

Consequently the following source-connected corollary follows immediately once badAll_power_bound is added to the BB6.Agent49FullSpectrum namespace:

~~~lean
theorem drainB_failure_power_bound (a b d : Nat)
    (h : drainB a b d = none) : 3 ^ a ≤ 2 * b + 1 := by
  have hflat : flatB a b d = none := by
    rw [← flatB_eq_drainB b a d]
    exact h
  exact badAll_power_bound a b ((flat_failure b a d).1 hflat)
~~~

The standalone file deliberately keeps its own namespace and exact copy of badAll; the wrapper above has **not** yet been integrated or compiled against the original Cryptids imports. Agent49 should integrate the theorem into FullFailureSpectrumSource.lean (or import this file and establish definitional equality) and run the existing source CI.

## Relevance to the blank-root problem

For any high-level branch whose final B-drain has first-counter input \(u\) and block count \(b\), termination therefore requires

\[
3^u\le 2b+1.
\]

Hence \(3^u>2b+1\) is a simple, uniform sufficient condition for that B-drain to survive. This gives a closed-form logarithmic envelope for terminal candidates and a compact arithmetic target for root-specific analysis.

It does **not** prove that every actual blank-root branch satisfies this inequality. The path-sensitive safeBudget(b) from Agent8's SafeBudgetSource.lean can be much smaller, so this theorem is a coarse universal bound rather than a replacement for that exact digit-path criterion.

## Verification

The standalone file was compiled locally with Lean 4.36.0-rc2. #print axioms for badAll_bounds, badAll_first_le_pow, badAll_power_bound, badBlock_fatal, and two_badBlock_add_one reports only Lean's standard propext and Quot.sound; there are no sorryAx or custom axioms.

This result belongs in im-results/, not results/: it is a verified structural lemma for the #623 drain, but it does not resolve the blank-root orbit or BB(6).
