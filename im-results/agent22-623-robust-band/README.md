# #623: unbounded fatal bands and a tuned three-evaluation synthetic halt

**Scope:** two all-parameter arithmetic conclusions for the original Cryptids #623 accelerated map, with a deliberate separation between **arbitrary constructed section entries** and the **authentic blank entry D(0,7)**. Neither establishes an all-time root decision or determines BB(6). The code belongs in \`im-results/\` until a root-connected proof or independent novelty evaluation warrants promotion.

## Main conclusions

Write \(\tau(n)=(3^n-1)/2\), which is Agent49's \`boundary n\`, and let \(\mathcal E_b\) be the set of first counters on which the original \`drainB\` fails for block count \(b\), independently of the third counter. Its exact total recursive predicate \`badAll\` and its equivalence to the unmodified Cryptids source are already formally proved in [Agent49's complete failure spectrum](../agent49-parity623/FullFailureSpectrum.md).

**Theorem A, a robust fatal band.** For all \(k,n,a,e,d\in\mathbb N\),

\[
a+2k+2\le n,\quad 0\le e\le 3^k
\quad\Longrightarrow\quad
\operatorname{drainB}(a,\tau(n)+e,d)=\mathrm{none}.
\]

Thus a **consecutive interval of \(3^k+1\) block counts**, beginning at the ternary all-ones boundary, is fatal simultaneously for **every first counter \(0\le a\le n-2k-2\)** and every third counter. Both the allowed block count and first counter range can grow without bound. The direct special case \(\operatorname{drainB}(3,\tau(2q+5)+8q+26,d)=\mathrm{none}\) holds for every \(q\ge1\).

The proof is strong enough to survive the carry of \(e\) under ternary division. The \`badAll\` recurrence sends a block congruent to 1 modulo 3 to the previous first counter and quotient \(b/3\); a block congruent to 2 sends a positive first counter to the previous first counter and quotient-plus-one, while at first counter zero it uses the unincremented quotient; a positive block divisible by 3 increases the first counter by one and reduces the quotient by one. Induction on \(k\) uses the slack of \(2k+2\) and the radix split \(e\bmod3\), with exact base cases at \(e=0,1\). A separate one-line exponential domination induction covers \(8q+26\le 3^q\) for \(q\ge4\); \(q=1,2,3\) are kernel-decided.

**Theorem B, an infinite synthetic three-evaluation halting family.** Let \(m\) be any even natural number and set
\[
t_m=\frac{3^{m+1}-3}{2}, \qquad x_m=3t_m+2=\frac{3^{m+2}-5}{2}.
\]
For the unmodified Cryptids high-level transition \(T=\mathrm{highLevelNext}\), the following are exact identities:
\[
\begin{aligned}
T(D(x_m,\,13x_m-2m+32))
  &=D(12x_m-m+34,\;3x_m+3),\\
T(D(12x_m-m+34,\;3x_m+3))
  &=D(9x_m+28,\;9x_m+23),\\
T(D(9x_m+28,\;9x_m+23))
  &=\mathrm{none}.
\end{aligned}
\]
Here the first two evaluations are successful returns; **the third evaluation fails**. Since \(t_{m+1}=3t_m+3\), the constructed initial states are pairwise distinct. Their first counters are even and the second state has an odd third counter.

The first two identities follow from Agent8's exact \`drainB_tight\` lemma and the same right-even/odd-far-left branch mechanism used in [Agent49's earlier two-step pole construction](../agent49-parity623/TwoStepPoleCancellationSource.lean). For the final call, the first counter of the drain is exactly zero and its block parameter factors as
\[
9x_m+26=3(9t_m+14)+2,\quad
9t_m+14=3(3t_m+4)+2,\quad
3t_m+4=3(t_m+1)+1.
\]
The two radix-3 digit-2 steps preserve first counter zero; the digit-1 step is immediately fatal. Consequently the third return is impossible for **every** even parameter \(m\), with no size or finite-horizon assumption.

These constructed starts illustrate that the exact affine-ray source equations can intentionally enter the fatal gate. They provide no evidence that the distinguished blank-root orbit ever visits one of these entries.

## Formal artifacts and verification boundary

- [\`Agent22RobustBand.lean\`](Agent22RobustBand.lean) provides a complete standalone Lean 4.36.0-rc2 kernel proof of the total recursive model, Theorem A and the explicit linear subfamily. Local output of \`#print axioms\` was exactly \`[propext, Quot.sound]\`; no \`sorry\`, \`sorryAx\`, or nonstandard axioms.
- [\`Agent22RobustBandSource.lean\`](Agent22RobustBandSource.lean) proves recursive equality between the independently copied fatality predicate and **Agent49's genuine \`badAll\`**, identifies the identical boundary recurrences, then composes Agent49's original-source \`drain_none_iff_badAll\`. The source adapter's complete proof was preflighted against exact-shape local stubs, and its source-pinned CI verification is tracked in [run 42638339174](https://github.com/FlareZ123/bb6/actions/runs/42638339174). **Do not cite the source adapter as pinned-source verified until that job succeeds.**
- [\`Agent22ThreeStepSource.lean\`](Agent22ThreeStepSource.lean) is a theorem over the original \`highLevelNext\` with existing Agent8/Agent49 source lemmas as imports. Its full Lean term assembly was checked locally using a source-shaped high-level function and *mock interfaces* for already-established external lemmas. The mock-based check is not a source certification. A pinned-source compilation should be run before advertising original-source kernel status.
- An independent exact Python mirror of the source recursions confirmed the three evaluations for all even \(m\) between 0 and 28, and a further 0..70 parameter scan checked the underlying tuning. These are diagnostics supporting the algebra, not a replacement for the quantified proofs.

## Relation to the actual BB(6) objective

The published original source proves that the six-state machine's blank halt is equivalent to a failed accelerated transition along the **specific** orbit from \`D(0,7)\`. Theorem A identifies extensive fatal *synthetic* drain cylinders, and Theorem B constructs a full trajectory to one such cylinder from an adjustable starting section. The unresolved quantifier is whether the genuine blank-root trajectory ever reaches **any** fatal gate. A useful next research target is to pull these exact failure bands backward through the original root chart while preserving the root's initial-state history. Exclusions or witnesses must remain rooted in \`D(0,7)\`.

**Source pin:** [google-deepmind/cryptids@c86f15861709b76042998c5211c7b2f83991621b](https://github.com/google-deepmind/cryptids/tree/c86f15861709b76042998c5211c7b2f83991621b). Avoid conflating the already-source-proved exact failure predicate with either new theorem's pending source-integration status.
