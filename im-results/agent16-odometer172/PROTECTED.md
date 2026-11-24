# Protected exceptional charges: reduction to bad births

A charge unequal to 1 need not be fatal. We give a sufficient all-time safety condition for internal gaps, preserved by every particle update other than the creation of a new front gap. This turns a prospective nonhalting proof for #172 into a single birth-guard obligation.

Use the particle encoding and notation of [README](README.md). A suffix beginning with a particle, excluding the gap immediately before it, has mass P = number of its particles + sum of all gaps after those particles (including its trailing gap). Let W=3P+w(s), with w(D)=1, w(L)=0, w(H)=2, where s is the first suffix phase. For the internal gap G between left particle A and this nonempty suffix, say it is **protected** if

```
G >= W + [phase(A) != H].
```

In particular protected implies strictly positive. Call an internal gap safe if its charge is 1 or it is protected.

## Proof of preservation

Consider the exact ordinary and collision moves from the word equations. When a non-birth move acts inside a suffix and leaves it nonempty, the mass P does not increase and W decreases by at least 1:
* First D->L: P unchanged, w decreases by 1.
* First L->H with positive gap: P decreases 1, w increases 2.
* First H carrying into a later particle or boundary: it resets to D, w decreases 1; any consumed gap decreases P.
* Pair annihilation removes 2 particles and merges gaps with one additional 2. Thus P drops at least 1 even if the pair is at the suffix front and the merge goes into its exterior gap. If the first particle changes, w can increase by at most 2.
* Last-particle drain removes 1 particle and can add at most 1 to a gap. If a nonempty suffix survives, its earlier first H resets to D, so W decreases even when P is unchanged.
* Birth at the global front leaves the suffix phases H, consumes 1 trailing 2 or drops the last particle while adding 1 to the preceding gap. W does not increase whenever the old suffix survives.

For a protected gap, moves strictly before A leave the data unchanged unless A is annihilated. At A's D->L move nothing changes in the protection inequality. At L->H, G decreases by 1 but the indicator decreases by 1. At a carry from A in phase H into its suffix, A resets to D and the inequality is preserved because W decreases at least 1. A birth with all H does not reset A and cannot increase W. If a pair inside the suffix at its front is removed, G can only increase (or ceases to be internal) and W decreases. If A is removed in an annihilation with the particle immediately to its left, the new merged gap includes G+1, and the suffix is unchanged; this pays any increase of at most 1 in the left-phase indicator. If the gap becomes leading or trailing it needs no protection. A collision across the protected gap is impossible since G>0.

Charge-1 gaps remain charge 1 under ordinary moves: earlier H->D resets change the next phase by -2 and the left H indicator by -1, while the active increment cancels the preceding reset; on L->H the gap decrease cancels the indicator increase. A pair at zero gap following an L must therefore have next phase L. The pair is safely annihilated. At an interior annihilation the merged charge is c_left+c_right-1 mod 3. If both exterior gaps were charge 1 the result is charge 1. Otherwise any protected exterior gap supplies protection for the merged gap by the preceding inequalities. Boundary drains remove only a trailing particle; existing internal charges are conserved with the same reset argument. For birth, surviving old internal charges are unchanged, but the new gap may have a different charge.

Therefore a safe state can take every move while preserving safety, except possibly a birth introducing an unprotected new gap with charge different from 1. All safe states have defined high-level successors; the root [0] has no internal gaps and is safe. Consequently any halt from the genuine root must be preceded by such an exceptional unprotected birth. This statement does not assume that the trajectory always has charge 1.

## Remaining single guard

At a birth with m>0, all phases H, B=0 and positive trailing gap, the new front gap is g0+1, charge g0+1 mod 3. The old suffix retains m particles and its trailing gap decreases 1. Hence the guard is exactly satisfied if either g0=0 mod 3 or

```
g0+1 >= 3(sum_{i=1}^m g_i - 1 + m)+2.
```

The zero-tail birth removes the last old particle and uses the corresponding reduced suffix; m=0 and m=1 cases with no new internal gap need no guard. The stronger sufficient inequality g0>=3(sum g_i+2m) works in either branch with a surviving internal new gap.

The first bad-charge birth at event 124075 satisfies even this stronger sufficient inequality: g0 divided by the pre-birth nonleading gap sum is approximately 3.762289011, and the exact integer margin against the stronger post-birth inequality with 2m is 25856493727883785084067016732350210029029508765288363583191374529443587011912762013940926433060396489919408380072. Its charge is thus protected until it vanishes or merges, provided other births satisfy the guard. This is a rigorous explanation of why the charge counterexample is not inherently fatal, rather than an extrapolation from its long persistence.

The leading residue l=(g0-s0) mod3 is preserved by ordinary increments and all-H wraps. A front birth resets l to 1. On a front pair annihilation with a surviving new first phase d, l'=l+c_next+d mod3, where c_next is the old gap charge between the removed second and the new first particle. This is the only nonboundary mechanism changing l. The root computation exhibits a front collision at time 53,222,495 changing l to 2, followed by a front collision at 53,344,117 restoring l=1. The much later front collision at event 124066 changes l to 2 and leads to the protected exceptional birth. A general proof that all such future births obey the guard remains open.

This is a written proof on the exact word/particle model, not a Lean-certified particle invariant. [Word.lean](Word.lean) independently checks the five direct word equations in Lean 4.36.0-rc2 against the copied upstream scan/return definitions (only propext and Quot.sound; the zero-empty case is axiom-free). No new machine verdict or BB(6) bound is claimed.
