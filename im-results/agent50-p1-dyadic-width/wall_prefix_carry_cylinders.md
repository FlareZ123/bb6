# Root-prefix carry cylinders for the fourth-edge restart families

**Status:** exact intermediate arithmetic result. The carry recurrence and all four infinite-cylinder exclusions are Lean-checked in core Lean 4.36.0-rc2. The short bridge from the existing source-wall list identity to the Boolean prefix is written out below but has not yet been composed into the source wrapper. This does not decide P1 or BB(6).

## 1. Source-wall reduction

The source-connected theorem `source_wall_cost_list_identity` in PR #99's branch (`im-results/agent43-p1-high-cost-reset-count/WallTelescopingSource.lean`, head `9c8ee112e4ead2bb8e6ec8b56d8f2a15a476271e`; CI run `45309147749`) gives, for a genuine right-five wall state, a duplicate-free list (A) of earlier inverse-cost starts with (0\in A), and the exact identity
[
1+7\,2^n\sum_{s\in A}2^s
=
2^{n+m}+\sum_{s\in A}(n+3+s)2^s+(n+3+m)2^m.
	ag{1}
]

Fix (K\le n,m). Reducing (1) modulo (2^K) kills the first term on the left and both explicit terminal terms on the right, so
[
\sum_{s\in A}(n+3+s)2^s\equiv1\pmod{2^K}.
	ag{2}
]
All starts (s\ge K) vanish modulo (2^K). Since (A) is duplicate-free, define (x_s\in\{0,1\}) by (x_s=1\iff s\in A), for (0\le s<K). The source fact (0\in A) gives (x_0=1), and (2) becomes
[
(n+3)+\sum_{s=1}^{K-1}x_s(n+3+s)2^s\equiv1\pmod{2^K}.
	ag{3}
]
The left side of (3) is exactly `bitExpr n rest` in the Lean file, with `rest` the Boolean list `[x₁,…,xₖ₋₁]`.

Thus, once the list-to-Boolean characteristic-map lemma is composed into PR #99, a Lean theorem excluding (3) excludes every source wall state with (K\le n,m). The carry certificate below supplies that arithmetic exclusion on four infinite parameter cylinders.

## 2. Exact carry certificate

Let
[
E_K(n,x)=(n+3)+\sum_{s=1}^{K-1}x_s(n+3+s)2^s,
\qquad x_s\in\{0,1\}.
]
Writing (E_j=1+2^j c_j) after the first (j) positions gives
[
c_1=(n+2)/2,\qquad
c_{j+1}=\frac{c_j+x_j(n+3+j)}2.
	ag{4}
]
At each position the zero choice is allowed exactly when (c_j) is even; the one choice is allowed exactly when (c_j+n+3+j) is even. The Lean function `carryStatesFrom` enumerates *all* resulting carries. The theorem `noBitSubset_of_emptyCarry` proves that an empty layer after (K-1) transitions rules out every Boolean prefix satisfying (3); it is not a heuristic search.

A second Lean lemma shows that the prefix expression changes by a multiple of (2^K) under (n\mapsto n+2^Kt). Consequently, one empty-layer certificate at (n_0) excludes the entire cylinder (n\equiv n_0\pmod{2^K}).

## 3. Four infinite cylinders excluded

The two local fourth-edge restart families from [`fourth_edge_terminal_survivors.md`](fourth_edge_terminal_survivors.md) are
[
\begin{aligned}
\mathrm{I}:&\quad n=5362+595056h,\
&\quad u=(17\cdot2^n-636)/1058,\[2mm]
\mathrm{II}:&\quad n=9538+703248h,\
&\quad u=(87\cdot2^n-712)/1198,
\end{aligned}
\qquad m=14u-2n-3.
]
Both are locally source-valid restart suffix families, not blank-root witnesses.

The Lean file proves the following four exclusions for every (t\in\mathbb N):

| Family | Parameter cylinder | Base (n_0) | Prefix modulus | First empty layer |
|---|---:|---:|---:|---:|
| I | (h=1+2^{56}t) | 600418 | (2^{60}) | 60 |
| I | (h=2+2^8t) | 1195474 | (2^{12}) | 12 |
| II | (h=1+2^{10}t) | 712786 | (2^{14}) | 14 |
| II | (h=2+2^{18}t) | 1416034 | (2^{22}) | 22 |

The arithmetic lifts are exact:
[
595056=16\cdot37191,\qquad 703248=16\cdot43953,
]
so the four (n)-values are respectively
[
600418+2^{60}(37191t),\
1195474+2^{12}(37191t),\
712786+2^{14}(43953t),\
1416034+2^{22}(43953t).
]
These are precisely the cylinders handled by `noPrefix_familyI_h1`, `noPrefix_familyI_h2`, `noPrefix_familyII_h1`, and `noPrefix_familyII_h2`.

### Checking the terminal-cost cutoff

For both restart families, (m=14u-2n-3). Substitution gives
[
1058m=238\cdot2^n-2116n-12078
\]
in family I, and
[
1198m=1218\cdot2^n-2396n-13562
\]
in family II. The existing source numeric bound (2^n\ge1100n) for (n\ge14) implies (m\ge n) in both cases (the residual lower bounds after subtracting (1058n) and (1198n) are (258626n-12078>0) and (1336206n-13562>0)). All four base indices satisfy (n\ge K), hence (m\ge K) as required to reduce (1) modulo the displayed prefix modulus.

## 4. Verification boundary and next step

- Lean source: [`wall_prefix_carry_cylinders.lean`](wall_prefix_carry_cylinders.lean).
- It imports only `Lean`; the carry completeness theorem, empty-layer computations, modulus lifts, and four family-cylinder statements are all kernel-checked locally with Lean 4.36.0-rc2.
- The four `#print axioms` outputs are exactly `[propext, Quot.sound]`; there is no `sorryAx`.
- The source identity (1) is independently present on PR #99's branch and its targeted workflow is green, but this invocation did not inspect successful-job logs or the `#print axioms` output; it therefore makes no claim that the source theorem is `sorryAx`-free. The characteristic-list-to-Boolean-prefix composition has not yet been added to that source wrapper; this is the remaining formal integration step.
- These four cylinders do **not** cover all (h) in either restart family. No unrestricted six-shallow theorem, P1 nonhalting proof, BB(6) upper bound, or exact BB(6) value follows.

The useful next action is to add the small `List.Nodup` characteristic-bit bridge to PR #99, apply the four Lean cylinder theorems, and then attack the still-uncovered (h)-classes. Do not rerun the earlier finite (n\le10{,}000) scan or repeat the fourth-edge 81-case classification.


The generic inequality (2^n\ge1100n) for (n\ge14), and both implications (m\ge n) from the explicit (u)-formulae, are now kernel-checked in the Lean file as `pow2_ge_1100_mul`, `familyI_terminal_m_ge_n`, and `familyII_terminal_m_ge_n`. Their `#print axioms` audits are `[propext, Quot.sound]`.


## Relation to the earlier full-wall carry convention

Put (P=2^n) and (Q=7P-(n+3)). Rearranging (1) gives the previously audited full-wall identity
[
\sum_{s\in A}(Q-s)2^s=2^m(P+m+n+3)-1.
]
For (K\le n,m), its right side is (-1\pmod{2^K}), while (Q\equiv-(n+3)\pmod{2^K}). Thus it is exactly the negative of (3), and the two prefix formulations are equivalent: the earlier (Q-s) carry tracks the all-ones target (-1\pmod{2^K}), while this Lean file tracks the cost-side target (1\pmod{2^K}).

The terminal convention is also consistent with the earlier audit: the terminal start (m) is separate from the earlier-start list (A), and the formally proved (m\ge n\ge K) means it cannot contribute to any of these prefixes. This avoids the (m<n) terminal-inclusion case discussed in the earlier full-wall audit.
