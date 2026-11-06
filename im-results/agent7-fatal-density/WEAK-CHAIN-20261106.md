# #746 source-C inverse growth and weak-margin odd-fork suppression

**Agent 7, 6 November 2026, 20:32 UTC. Classification: intermediate; not an exact BB(6) solution, a global exclusion, or a new literature-audited machine decision.** All formal statements use the original complete source-C reset semantics from `FirstInverseComplete.lean` and the genuine post-initial blank reset `(2,0)`.

## Checked source arithmetic: sharp forward reset growth

[ResetEnvelope.lean](ResetEnvelope.lean), [source CI 42284651273](https://github.com/FlareZ123/bb6/actions/runs/42284651273) (success), proves the universal complete predecessor disjunction. For each even exact parent at scale k, `h+k+3<=u`. For each odd parent at scale k and 3-adic drain length t, `3*h+3*k+13<=2*u` and `3^(t+1)*(h+k+6)<=2^t*(2*u+5)`. Both non-valuated bounds are sharp for **every scale k**, by exact `ResetParent` constructions, and come from the original `Outcome`-equivalent arithmetic grammar. Ordinary proof axioms only; `sorryAx` absent. No bound on the entire inverse-cone size or rooted reachability follows.

## Checked genuine-root arbitrary-length gap criterion

[EvenChainGap.lean](EvenChainGap.lean), [source CI 42286452067](https://github.com/FlareZ123/bb6/actions/runs/42286452067) (success), defines the genuine fixed-scale even inverse recurrence
```
E=8*2^k+k
q_0=q
q_(i+1)=2*q_i-E
```
and the explicit safe mod-three condition `q%3 != 2 && (E%3==2 || q%3==E%3)`. If every `q_i` before step r is inside the exact even-return image band `[6*2^k-1,8*2^k-3]`, the theorem `walk_root_iff` proves the genuine source blank-root relation is equivalent for `q` and `q_r`. If `q_r` falls strictly between `4*2^k-3` and `6*2^k-1`, then `walk_exits_gap_unreachable` proves **not reachable** from the actual `(2,0)` root. The band is disjoint from every even reset image, and mod-three excludes all odd reset images. This uniformly handles any natural chain length r and does not omit high-valuation inverse branches.

## Weaker-margin two-tier use and concrete example

[EvenChainFork.lean](EvenChainFork.lean) composes the prior all-time source `offray_fork_root_iff_second_tone` with the unbounded chain-gap criterion, for ray margin `32*D+64*n+128<=2^n`, `n>=13`, exact two t=1 valuation gates and explicit valid fixed-scale exit conditions. It proves `weak_margin_two_tier_gap_dead`: the physical off-ray t=1 parent `h` is blank-root inaccessible. **Source CI verification of this extension was in progress at the time of this note**; check the run's conclusion before claiming this file is fully checked.

Example: `n=28,j=16,D=3866597,2^n=268435456`; weak-margin lhs `123733024` is below `2^n`, whereas Agent10's stronger `2048*D+16384*n+16384=7919265792` is above `2^n`. Exact source ray target `U=1069875227` has t=1 odd parent `h=414129261`, whose forced even parent is `w=291387584`. Its unique t=1 odd inverse has `k=24,d=64752797,q=124793431`, with mod-three safe residue `q%3=1`. The two forced even ancestors are `115369110` (still inside the image band) and `96520468` (inside the universal no-even-image gap). Both t=1 source numerator gates have low 3-adic order: `(2*h+5)%27=20`, `(2*w+5)%27=18`.

A separate [EvenChainForkSpecial.lean](EvenChainForkSpecial.lean) attempts to prove **every** source odd parent of this exact ray point is blank-root excluded: t=0 and t=2 have their input outside all odd image bands; t=1 reduces to the above h; t>=3 is ruled out because `(2*U+5)%81=27`. Pending full original-source CI. Even if verified, the canonical even predecessor route remains unresolved, and historic finite fatal-index exclusions may already imply this single example. The general lossless weak-margin fork lemma is the reusable contribution.

## Further arithmetic observation, not a theorem

For physical `D=2^j*(2*n+3)-(n-1)` and valid second t=1 ancestor, let `p=2^(n-4)` and `B=8*p-q`. Exact algebra gives
```
81*B = 16*p + 128*2^j*(2*n+3) + 169*n - 3.
```
The dyadic gap is hit by 2, 3 or 4 even steps unless the normalized deficit lies in very thin O(n) transition windows near `B=p/2` or `B=p/4`. At those boundaries, the equation requires `2^j*(2*n+3)` to approach respectively `49*2^(n-12)` or `17*2^(n-13)` to within O(n). Their large common 2-power and the oddness of `2n+3` suggest a possible uniform elementary exclusion of these windows. **The uniform no-window statement has neither been proved nor independently verified.** The exact equation above is algebraic; claims about all window avoidance require further proof.

Exploratory deterministic Python checked admissible weak-margin pairs with `13<=n<=3000` in surviving n mod6 sectors. Among 18,351 second-level low-valuation t=1 candidates, 16 exited after 2 steps, 32 after 3, and 18,303 after 4; no other exits were observed. Another 9,174 candidates had w divisible by27 and remain completely untreated by this mechanism. These finite samples do not constitute a uniform bound or rooted proof. Preserve the exact script if extending the census.

## Global status

The #746 blank-root halting question is still unresolved across all fatal indices. Higher-valuation odd parents, high-margin canonical continuation, other six-state machines, a complete global coverage certificate, and an exact champion-score witness remain separate open requirements for BB(6). Keep these structural results under `im-results/`, subject to novelty assessment.
