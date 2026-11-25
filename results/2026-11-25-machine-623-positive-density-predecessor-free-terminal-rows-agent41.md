# A positive-density family of predecessor-free terminal rows for machine #623

## Result

Let E : ℕ → ℕ satisfy the exact excess recurrence
\[
E(0)=0,\quad
E(3q)=E(q-1)\ (q>0),\quad
E(3q+1)=4+E(q),\quad
E(3q+2)=2+E(q+1),
\]
and define the drain image F(b)=3b+E(b). Let inv(y) be the exact partial inverse of F: it is b precisely when F(b)=y, and is undefined otherwise.

For each row d define the two possible terminal gates
\[
G_{\mathrm{even}}(b)=F(b)+
\begin{cases}2&b\text{ even},\\3&b\text{ odd},\end{cases}
\qquad
G_{\mathrm{odd}}(b)=F(b)+
\begin{cases}5&b\text{ even},\\0&b\text{ odd}.\end{cases}
\]
A row d is blocked when
\[
\begin{aligned}
d\text{ even}:&\quad
\operatorname{inv}(d-2)=\varnothing
\ \land\ \operatorname{inv}(d-3)=\varnothing,\\
d\text{ odd}:&\quad
\operatorname{inv}(d-5)=\varnothing
\ \land\ \operatorname{inv}(d)=\varnothing.
\end{aligned}
\]
Let
\[
\mathcal G_N=\{d<18N:\ d>14,\ d\bmod6\in\{1,2\},\ d\text{ is blocked}\}.
\]

**Theorem.** For every N in the natural numbers,
\[
|\mathcal G_N|\ge 2N-6.
\]
Moreover, for every d in G_N, the corresponding source macro-state
\[
D(\operatorname{terminalFirst}(d),d),\qquad
\operatorname{terminalFirst}(d)=
\begin{cases}d+2&d\text{ even},\\d+5&d\text{ odd},\end{cases}
\]
is terminal under the exact source macro-transition, has no predecessor of the form D(a,e), and is never visited by the authentic blank-root macro-run of machine #623.

Consequently, the parameter set of these root-inaccessible terminal rows has lower density at least 1/9 among all natural row indices. Since the admissible terminal-row family d mod 6 in {1,2} has density 1/3, the relative lower density within that family is at least 1/3.

## Proof structure

The inverse-image combinatorics is exact. For every q>0, the three same-parity arguments
\[
b=3q-1,\quad b+2=3q+1,\quad b+4=3q+3
\]
have image values
\[
F(b),\quad F(b)+8,\quad F(b)+10.
\]
This follows directly from the three clauses of the excess recurrence and the exact two-step image-gap lemma.

If a terminal-congruence row d is not blocked, one of its two inverse candidates exists. Parity of F(b) then places d in the even or odd gate family. Among the three offsets 0, 8, 10, at most one can meet the required residue for the even gate and at most one can meet the required residue for the odd gate. Thus, for each q, all unblocked rows arising from this triple are contained in a two-element list. The six base rows 1, 2, 7, 8, 13, 14 are handled separately.

For rows below 18N, only q≤2N is needed. The explicit gate-cover list therefore has length 2(2N)+6=4N+6. There are exactly 6N rows below 18N congruent to 1 or 2 modulo 6. At most 4N+6 can be unblocked, so at least 6N-(4N+6)=2N-6 are blocked.

The source bridge then supplies the machine-specific conclusion. The terminal-budget lemma places terminalFirst(d) inside the exact inverse-envelope range. The source terminal-gate theorem proves that D(terminalFirst(d),d) has no next macro-state. The two-shift predecessor theorem shows that a blocked row has no incoming macro-edge from any D-state. Finally, induction on the authentic source macro-run excludes every such state from the blank-root orbit.

## Density calculation

For X≥0, take N=floor(X/18). Then 18N≤X, so G_N is contained in the blocked terminal-row set below X and
\[
\#\{d<X:\ d>14,\ d\bmod6\in\{1,2\},\ d\text{ blocked}\}
\ \ge\ 2\lfloor X/18\rfloor-6.
\]
Dividing by X and taking the lower limit gives at least 1/9. The admissible terminal rows themselves occupy asymptotic density 1/3, giving relative lower density at least 1/3 inside that family.

This density is over the row parameter d for one fixed machine. It is not a density of six-state machines or of all tape configurations.

## Formalization and source acceptance

The exact inverse and image-gap facts are in [DrainImageDecoder.lean](../im-results/agent41-623-3euclidean/DrainImageDecoder.lean); the two-shift gate and finite density count are in [DrainImageAP.lean](../im-results/agent41-623-3euclidean/DrainImageAP.lean) and [DrainImageDensity.lean](../im-results/agent41-623-3euclidean/DrainImageDensity.lean). The source adapters are [DrainImageSource.lean](../im-results/agent41-623-3euclidean/DrainImageSource.lean), [FatalBandSource.lean](../im-results/agent41-623-3euclidean/FatalBandSource.lean), and [FatalDensitySource.lean](../im-results/agent41-623-3euclidean/FatalDensitySource.lean). The final theorem is BB6.Agent41FatalBand.terminal_density.

The complete decoder source closure passed [CI run 45552009439](https://github.com/FlareZ123/bb6/actions/runs/45552009439), using the unmodified Cryptids machine source pinned at commit c86f15861709b76042998c5211c7b2f83991621b and Lean 4.35.0-rc4. The workflow captured the #print axioms output and rejected sorryAx or native_decide; the run succeeded. The standalone arithmetic core had also been checked with Lean 4.36.0-rc2.

## Scope and remaining problem

This theorem excludes a positive-density infinite family of terminal macro-states from the authentic blank-root orbit. It does not prove that every terminal row is blocked, does not prove machine #623 nonhalting, and does not provide a universal upper bound for BB(6). The remaining challenge is to analyze the nonblocked terminal rows and their exact parent branches, then establish a complete all-time event partition for the authentic root.
