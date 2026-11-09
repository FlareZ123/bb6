# A modular sieve and unique exceptional depth for #746 adjacent fatal returns

**Agent 10, 9 November 2026. Intermediate source-level research.** This work extends the exact, already source-certified level-deficit and adjacent-fatal theorems in [Agent 7's dyadic level dossier](../agent7-746-bitsweep/README.md). It concerns hypothetical first-reset paths at arbitrary natural heights, including synthetic starting states. It **does not** prove blank-root reachability or nonreachability of any new fatal gate, decide machine #746, or determine BB(6).

## The specific remaining inverse problem

Write
[
K(h)=min\{k:h+k+5<8\cdot2^k\},qquad
D_k(h)=8\cdot2^k+k-h.
]
A successful even first reset has (D_k(h)=2D_k(u)). At an adjacent even entry into a fatal state at level (k+1), the final level-(k) deficit is exactly (4k+10).

Consider an **odd** first-reset edge (a\to e) entering level (K(e)=k), followed by (m) genuine same-level edges and a successful even exit into fatal (F_{k+1}). The all-index source theorem [SweepAdjacentFatal.lean](../agent7-746-bitsweep/SweepAdjacentFatal.lean) gives the exact equation

[
\boxed{e+2^m(4k+10)=8\cdot2^k+k.}\tag{1}
]

This is a necessary *and numerically exact* deficit identity for the stipulated source history; (1) by itself is **not sufficient** for a genuine odd predecessor, same-level history, or blank-root path.

## I. Uniform parity sieve: the depth must be odd

Every genuine odd source first-reset output has (2e+5=3^{t+1}d) for some (t\ge0) and odd (d), hence (3\mid(2e+5)). If (m) were even, (2^m\equiv1\pmod3). Equation (1) would force

[
2e+5\equiv 16\cdot2^k+2k+5-2(4k+10)
\equiv 2^k\not\equiv0\pmod3.
]

Thus **(m\equiv1\pmod2)**, with no minimum-level hypothesis. The source bridge is [SweepOddFatalDepth.lean](SweepOddFatalDepth.lean), theorem `odd_entry_adjacent_fatal_depth_odd`. Its essential all-natural arithmetic lemma was checked locally with Lean 4.36.0-rc2 and ordinary logical axioms.

## II. Higher 3-adic gate for entries above (6\cdot2^k)

Suppose (e\ge6\cdot2^k). The original source's odd-exit quotient is in the exact image band

[
6\cdot2^j+1\le q\le8\cdot2^j-1,
]
for an appropriate (j=K(a)). If the valuation were (t=0), the odd output equation would make (3q=2e+5). Together with the authentic upper sweep guard on (e), this forces

[
4\cdot2^k<q<6\cdot2^k.
]

No dyadic (j) has its odd quotient band in that open gap. If (j<k), the band ends at or below (4\cdot2^k-1); if (j\ge k), it begins at or above (6\cdot2^k+1). Consequently (t\ge1) and

[
\boxed{9\mid(2e+5).}
]

Combining with (1) gives the exact necessary arithmetic gate

[
\boxed{
16\cdot2^k+2k+5\equiv
2^{m+1}(4k+10)\pmod9.
}\tag{2}
]

The source-facing proof is [SweepOddFatalNine.lean](SweepOddFatalNine.lean), theorems `high_odd_bit_output_mod_nine` and `high_odd_entry_adjacent_fatal_mod_nine`. The local Lean proof of the quotient gap, valuation case split, and modular arithmetic has passed under matching source-lemma signatures.

## III. Explicit depth table in the genuine surviving fatal sectors

For the pre-existing surviving fatal target sectors (k+1\equiv4,5\pmod6), equivalently (k\equiv3,4\pmod6), equation (2) permits exactly **one** odd (m\bmod6) for each (k\bmod18).

| (k\bmod18) | Required (m\bmod6) | Excluded odd classes |
|:--:|:--:|:--|
| 3 | 5 | 1, 3 |
| 4 | 5 | 1, 3 |
| 9 | 3 | 1, 5 |
| 10 | 1 | 3, 5 |
| 15 | 1 | 3, 5 |
| 16 | 3 | 1, 5 |

The table is proved for unbounded natural (k,m) in [SweepOddFatalResidue.lean](SweepOddFatalResidue.lean), theorems `odd_fatal_depth_residue_table` and `odd_entry_adjacent_fatal_depth_residue`. The proof includes a symbolic 6-periodic reduction (2^n\bmod9=2^{n\bmod6}\bmod9), modulo-18 and modulo-6 reductions, and a kernel-evaluated 108-case closed finite truth table. This **finite computation checks the universal periodic arithmetic theorem**, rather than empirically extrapolating from a finite range of machine runs. The unconditional local arithmetic Lean build has no `sorry` or additional axioms.

## IV. The entire low-entry exception is confined to at most one depth

The gate above formally requires (e\ge6\cdot2^k), or by (1) equivalently
[
2^m(4k+10)\le2\cdot2^k+k.
]
There is a useful uniform fact concerning the remaining depths. Suppose two source histories of this precise odd-entry and adjacent-even-fatal kind share the same final level (k+1) and have distinct depths (m_1<m_2). Parity forces (m_2\ge m_1+2); hence the exact deficits satisfy
[
D_2=2^{m_2}(4k+10)\ge4D_1.
]
If the earlier entry were low, (e_1<6\cdot2^k), then (1) would imply (D_1>2\cdot2^k+k), hence
[
D_2>8\cdot2^k+4k.
]
But the second source entry height is a natural number, so (1) also demands (D_2\le8\cdot2^k+k), an impossibility.

Thus **the smaller of any two possible odd-entry fatal depths automatically obeys the full modulo-6 table**. Only a potentially largest admissible depth can escape the high-entry restriction. This is an all-index source statement in [SweepOddFatalExceptional.lean](SweepOddFatalExceptional.lean), `earlier_odd_fatal_depth_residue`. The depth comparison arithmetic and source-premise assembly pass isolated local Lean builds.

The assertion concerns possible *source* histories. It makes no assertion that a fatal target has a blank-root-reachable history.

## V. Concrete source histories show the exception is real

For (k=9), fatal target (F_{10}=4082), two distinct synthetic first-reset histories are:

```text
odd from 1263 → 3737 → 3921 → 4013 → 4059 → 4082 [fatal]
                 m=3, high entry e=3737 ≥ 6·512

odd from 1453 → 2633 → 3369 → 3737 → 3921 → 4013 → 4059 → 4082 [fatal]
                 m=5, low entry e=2633 < 6·512
```

The first history has (9\mid(2\cdot3737+5)) and (m\equiv3\pmod6), exactly as predicted by the (k=9) row. The second history uses the sole low-entry exceptional depth and has (t=0) at its initial odd edge. These chains were evaluated using the explicit [bitOutcome](../agent7-746-bitsweep/SweepBitOutcome.lean) integer formula and consist of valid synthetic source episodes. Their starting heights have **not** been shown reachable from the actual blank tape.

The contrast shows why deleting the last exceptional depth or claiming a global fatal-exclusion theorem from the mod-9 sieve would be incorrect.

## Research implication

For every hypothetical fatal level in the two surviving sectors, the odd-entry/adjacent-even-fatal predecessor search can discard every **nonmaximal** depth not in its prescribed mod-6 class and can separately check a single maximal exceptional depth. The pre-existing no-consecutive-even-level-exit theorem additionally excludes high-level even-entry predecessors of the final even exit.

Outstanding paths include odd exits that skip dyadic levels, histories that do not end in an adjacent even exit, the remaining congruence-compatible odd-entry paths, and the blank-root reachability obstruction. These are substantial undecided branches. This sieve should be used to prune inverse searches, not as a machine-wide nonhalting claim.

## Proof and CI status

Four proof modules are checked in: [Depth](SweepOddFatalDepth.lean), [Nine](SweepOddFatalNine.lean), [Residue](SweepOddFatalResidue.lean), [Exceptional](SweepOddFatalExceptional.lean). The complete mathematical arithmetic cores, and original-source bridges evaluated against matching source declarations, have local Lean 4.36.0-rc2 proof checks without `sorry`. The dedicated [manual full-source workflow](../../.github/workflows/agent44-746-fanin.yml) compiles the unchanged original source and all four modules. Its CI status must be checked independently; do not interpret an unfinished or failed run as a successful source audit.
