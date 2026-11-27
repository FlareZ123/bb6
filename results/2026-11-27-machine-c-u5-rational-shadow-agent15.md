# Rational negative-shadow certificates for the Machine C U5 residual

**Accepted original-source Lean result:** [run 45919729244](https://github.com/FlareZ123/bb6/actions/runs/45919729244) at commit `deeab8507f7dc45a7c29cd95bfad5e9614197cc1`, using the complete original source closure and rejection of `sorryAx`/native axioms. This is an infinite-family conditional exclusion theorem, not a decision of Machine C or of BB(6).

## Main theorem

Let natural numbers w,s,m satisfy

    211*s + 129 = 5*2^(201+3360*w)
    32*s = 32+840*w+m.

These are the previously reduced U5 residual conditions. Put E=201+3360*w, t=m/8, X=(44*t-1,42*t-1). Exact arithmetic gives

    211*t+1360+22155*w=20*2^E.

The new source theorem `high_stop_excluded_of_x` reduces reachability of the actual high m=0 stopping pair (2(39+64s)+3,3(39+64s)+7) to reachability of X. The proof composes the complete source y=3 parent fan, the six-even-right chain (simplified by conserved weighted mass), and the exact two-parent root pullback.

Define S=(44(1360+22155w)+211,42(1360+22155w)+211). Then 211 X.x+S.x=880*2^E and 211 X.y+S.y=840*2^E. No huge positive counter need be constructed. The complete predecessor cone is transported through congruence modulo 2^b using the two positive numerator coordinates of a negative rational shadow of denominator 211. Direct branches charge 1 bit; high branches of depth n charge n+2 bits. The guard 212(S.x+S.y+1688)<2^b prevents special small-coordinate or pure-power branches. Leaves use the exact original-source odd-image obstruction.

The resulting `u5_shadow_high_stop_excluded` says that acceptance of the executable checker at any fuel f implies nonreachability of the original stopping pair. `u5_shadow_high_stop_cylinder` is stronger for symbolic use: acceptance at a small representative z with precision b implies exclusion for **every** w congruent to z modulo 2^b, subject to b≤E. These theorems are source-connected and verified; universal acceptance remains open.

## Independent finite computations

The separate fixed-period affine filter is source-verified and excludes every w with `wFilter w=true`, periodic modulo 65536. Executable census: 54,715 of 65,536 classes (83.4885%). Previously established exclusions overlap, so this is not a count of newly excluded classes.

Independent integer implementations of the rational shadow search completed all 10,000 parameter trees for 0≤w<10000, within their exact bit budgets. The largest completed tree (w=4081) has 161,798,137 nodes and requires 49,060 bits, versus available 13,712,361. This computational census is not a Lean-reflected proof of the finite prefix. The conditional certificate theorem is formally verified.

## Source and remaining obstacle

- [Rational checker and generic soundness](../im-results/agent15-c-halting/RationalShadow211.lean)
- [Original stopping-pair lift](../im-results/agent15-c-halting/U5RationalHighStop.lean)
- [Periodic affine filter and common source pullback](../im-results/agent15-c-halting/U5AffineHighStop.lean)
- [Derivation, reproducible computations and exact limits](../im-results/agent15-c-halting/RationalShadow211.md)

The new method removes dependence on a fixed modulus and transforms the exponential U5 parameter into a small integer search with explicit precision. To close this family, a universal bound on all shadow inverse paths is still required (or another argument covering the complement). Neither the low family nor all other high families are decided by these results.
