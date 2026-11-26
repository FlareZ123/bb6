# Machine C: odd-depth mass-four low-gate exclusion

## Formal theorem

For all natural numbers n, k, u, q, if

- n ≥ 3 and n is odd;
- u = 6n + 7 + 48q;
- 3k = 2^(n+2)u + 1;

then the original Machine C blank-section reachability predicate satisfies ¬CReach(1,k).

The theorem is formalized as BB6.Agent31OddDepthTower.odd_gate_dyadic_tower_mass4_no_blank in [LowOddDepthTower.lean](../im-results/agent31-c-odd-depth/LowOddDepthTower.lean). It compiled with Lean 4.36.0-rc2 in source CI [run 45785695121](https://github.com/FlareZ123/bb6/actions/runs/45785695121). The proof uses original-source inverse equivalences and the source-accepted even-even sum-zero parent exclusions; it is not a simulation or finite-depth reachability approximation.

## Proof mechanism

The odd/odd source inverse sends (1,k) to

- a = (k - 3)/2,
- b = (3k - 9)/4,

with b + 2 = 2^n u and (a + 2b + 4n) mod 8 = 4.

Iterating the exact even-right inverse n-1 times gives a terminal pair (A,B) with

- B + 2 = 2u,
- A + B + 4n + 2u = a + u*2^(n+1) + 2.

In this specialization A and B are both 0 modulo 8, so A+B=8S for an integer S≥4, and A>5.

Write n=2t+1 and choose w with 2^(n+3)=64+96w. The terminal-sum identity becomes

24S + 12n = u(58+96w) + 2.

Substituting u=6n+7+48q and expanding gives

S = 28t + 31 + 4((6n+7)w + 29q + 48qw),

hence S=3 modulo 4.

The mass-residue-four cone is inductive: each nonterminal even-right state has the exact source predecessor required to continue the tower. At the terminal even-even state, the source-accepted blank_no_sumzero_target theorem reduces reachability to two parents:

- D = (8S - 2, u - 2),
- E = (2S - 2, 3S + u - 5).

Both have odd right counter and coordinate sum 1 modulo 4, so blank_no_odd_sum_one excludes both. Thus the terminal state, and inductively the original gate state, cannot be reached from blank.

## Connection to the low-stop parameterization

The low-stop linear relation has the exact integer solution (n,m,r)=(3,251,19):

9m + 13 + 5*2^(n+2) = r*2^(n+4).

For this seed,

- u = 3*2^(2m-n+1) + 5 - 4r = 3*2^500 - 71 = 25 + 48*(2^496 - 2);
- k = 2^(2m+3) - 3m - 4 = 2^505 - 757;
- 3k = 2^(n+2)u + 1.

It therefore falls under the formal theorem. This particular seed is also caught by the existing adaptive 32-bit modular low-stop checker; its role here is to exhibit the theorem's intersection with the stop parameterization, not to claim a new finite-census exclusion.

## Scope and remaining work

This is an unbounded odd-depth family, complementary to the existing even-depth dyadic low-gate theorem. It does not prove that every odd-depth low gate is unreachable, close the full low-stop existential, settle the remaining Machine C high-stop branch, or establish a BB(6) upper bound. The exact value of BB(6) remains unknown. The added content is the source-exact mass-residue-four terminal-parent argument and its symbolic all-depth residue class u = 6n+7 modulo 48.
