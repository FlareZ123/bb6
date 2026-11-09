# Machine #746: an exact high-band odd-image law and an infinite blank-root exclusion

**Formal mathematical result, 9 November 2026.** Machine: `1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA`, interpreted through the exact original source-C first-reset semantics. The blank-origin reset root is height 2. Lean 4.36.0-rc2 checked the complete original-source proof chain in [CI 42595867922](https://github.com/FlareZ123/bb6/actions/runs/42595867922), including the new unbounded-family theorem and all necessary source equivalences. The relevant `#print axioms` results contain only `propext`, `Quot.sound` and inherited `Classical.choice`; none contain `sorryAx`.

## Theorems

Write `K(u)` for the least `k` with `u+k+5<8·2^k`. The authenticated deterministic reset successor is `bitOutcome`. An *odd source parent* of `u` is a height `a` such that `(a+K(a)) mod2=1` and `bitOutcome(a)=some(u)`.

**Theorem 1 (complete upper-image law).** For every `u` with `k=K(u)≥2` and `u≥6·2^k`,

```text
u has an odd source parent  iff
  [27 | (2u+5)  when 4u+10 < 27·2^k]
  [ 9 | (2u+5)  when 4u+10 ≥ 27·2^k].
```

The inverse grammar states `q=2^t d`, with `d` odd, `2u+5=3^(t+1)d`, and `6·2^j+1≤q≤8·2^j−1`. The `t=0` quotient for `u≥6·2^k` occupies a strict empty dyadic inverse gap `(4·2^k,6·2^k)`. On the lower high band, `t=1` occupies a second gap `(2·2^k,3·2^k)`. Conversely the corresponding `t=2, j=k−2` and `t=1, j=k−1` exact inverse candidates satisfy every source guard whenever the respective divisibility condition holds. These are constructive equivalences, independent of blank-origin assumptions. Source theorem: [`entire_high_odd_image_iff`](../im-results/agent7-746-fatal-depth-27/SweepOddFatal27Upper.lean).

**Theorem 2 (uniform blank-origin exclusion).** For all `k≥3` and `e` with `K(e)=k`, if

```text
12·2^k+k+4 ≤ 2e,
4e+10 < 27·2^k,
(2e+5) mod27 ≠ 0,
(2e−8·2^k−k) mod3 ≠ 2,
```

then `¬ ReachC (2,0) (e,0)`. The first-reset root chain cannot enter `e`, even when `e mod3=2`. Indeed the first theorem eliminates *all* odd source parents of `e`. Its sole possible even parent is `h=2e−8·2^k−k`, using the globally unique even-image scale. The displayed interval forces `4·2^k−3<h<6·2^k−1`, which is disjoint from **every** even-return image band at any scale. The final congruence eliminates every odd source parent of `h`. Therefore `h` has no parents and cannot belong to the authentic blank-root reset chain. Source theorem: [`narrow_high_root_gap_exclusion`](../im-results/agent7-746-fatal-depth-27/SweepOdd27RootGap.lean).

**Theorem 3 (explicit unbounded exclusion).** For every `n∈ℕ`, set `k_n=9+54n` and `e_n=6·2^(k_n)+k_n+2`. Then

```text
¬ ReachC (2,0) (e_n,0).
```

The elementary integer inequalities for Theorem 2 hold uniformly for `k_n≥9`. Periodicity `2^(9+54n) ≡26 (mod27)` gives `(2e_n+5) mod27=15`; the forced even predecessor is `h_n=4·2^(k_n)+k_n+4`, with `h_n mod3=0`. Thus every member is excluded, and the strictly increasing `k_n` produce an infinite set of distinct excluded reset heights. In addition, **`e_n mod3=2`** for every `n`, showing that the older coarse mod3 odd-image obstruction does not already supply this exclusion. Source theorem: [`narrow_high_infinite_root_exclusion`](../im-results/agent7-746-fatal-depth-27/SweepOdd27RootFamily.lean). The source-certified finite member `n=0` gives `e_0=3083`.

**Corollary (narrow adjacent-fatal depth sieve).** For an authentic odd entry `a→e` into the lower high band followed by `m` successful same-level first resets and an adjacent even exit to fatal, the exact deficit identity implies

```text
16·2^k+2k+5 ≡ 2^(m+1)·(4k+10) (mod27).
```

The previously proved necessary sector `k mod6∈{3,4}` and periodicity of powers of two modulo 27 force exactly **one `m mod18` class per `k mod54` class**, as source-certified in [`narrow_odd_entry_adjacent_fatal_depth_27`](../im-results/agent7-746-fatal-depth-27/SweepOddFatal27Source.lean). This condition refines the pre-existing Agent 10 mod9 depth sieve in its narrower high-entry interval. The complete class table and an exact synthetic compatible history at `k=105,m=97` are in the [focused evidence dossier](../im-results/agent7-746-fatal-depth-27/README.md).

## Relation to earlier results and remaining open question

This root-exclusion method combines the existing [exact even-image scale and parent grammar](../im-results/agent7-cascade-forward/UniqueEvenBand.lean) and [source-complete reset-chain correspondence](../im-results/agent10-cascade/ResetChain.lean) with a new two-threshold 3-adic odd-image classification. Earlier Agent 7 direct-fatal congruence results in [`FirstFork.lean`](../im-results/agent7-cascade-forward/FirstFork.lean), Agent 7 forced-even gap methods in [`EvenChainGap.lean`](../im-results/agent7-fatal-density/EvenChainGap.lean), and Agent 10 high-odd-entry mod9 work in [`SWEEP-ODD-FATAL-DEPTH.md`](../im-results/agent10-cascade/SWEEP-ODD-FATAL-DEPTH.md) are distinct premises or antecedents. A genuine infinite blank-origin exclusion strengthens the source-only necessary gates without deciding all fatal levels.

**Scientific boundary:** These theorems exclude an infinite class of genuine #746 blank-root reset heights. They do **not** decide the complete #746 blank-tape halting question, the exact six-state Busy Beaver step count, or universal maximality. Externally established novelty and a complete paper exposition require independent review; the source and exact statements are available for that review.
