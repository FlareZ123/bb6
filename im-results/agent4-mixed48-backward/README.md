# Compact M48 backward invariant, source certified, parity-redundant

**Status 2026-11-04:** All proof obligations passed Lean 4.36.0-rc2 against the unmodified original checked-in `BB6CLine` source in [manual CI 41756442481](https://github.com/FlareZ123/bb6/actions/runs/41756442481). This is a useful independent reverse-invariant mechanism, **not a new Machine C halting exclusion** compared with Agent38's earlier certified `blank_section_no_33` theorem. It belongs in `im-results/`.

The authentic blank root is `(5,0,1)`. [BackwardMod48.lean](./BackwardMod48.lean) proves a universally backward-closed set with only the following modular conditions:

- At `c<2`, `a%16=3 and (k+c)%24=7`, or `a%16=11 and (k+c)%24=19`.
- At `c>=2`, write `d=(a+24-c%24)%24`, `t=(a+k)%48`; require `(d,t%12)` in `{(0,7),(8,3),(16,11)}`.

The complete representative quotient has `48 * 48 * (24+2)=59,904` states, with exactly `600` states in this reverse-closed core (24 low, 576 high). The count is a C++/Python finite check; kernel verification is the independent all-natural Lean implication `backward_step` for the unchanged Machine C transition rule, plus the fact that the blank root lies outside the set. [SourceBridge48.lean](./SourceBridge48.lean) transports this to `BB6CLine.Reach`.

[Stop48.lean](./Stop48.lean) proves, for the actual exact high-stopping equation
`k+j+3*m+5=2^(2*m+2)*(j+3)`, all `j%4=0,m%8=4` stopping gateways are unreachable on the authentic blank orbit. The argument uses the exact power residue 16 modulo 24 for all `m>=2`. This theorem is independently source-certified and axioms were audited.

**Crucial overlap:** Under the same stopping equation and parameter restrictions, elementary congruences also imply `a=2j+3≡3 (mod4)` and `k≡3 (mod4)`. Agent38's **earlier** original-source Lean theorem `BB6Agent38.blank_section_no_33` already excludes every such section input, without this M48 core; see [Agent38's original-source result](../agent38-c-section-mod4/README.md) and [CI 41434342391](https://github.com/FlareZ123/bb6/actions/runs/41434342391). Therefore the M48 theorem supplies an independent simple backward proof but no additional excluded halting parameters.

The practical research lesson is to check candidates against Agent38's global parity invariant before investing effort in deeper residue proofs. The 120 nonparity-obvious cells isolated in [Agent4's distinct mixed192 work](../agent4-mixed192-backward/README.md) avoid this specific redundancy. Neither construction resolves Machine C globally or BB(6).
