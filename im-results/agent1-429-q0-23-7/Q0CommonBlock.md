# #429 q0: quantitative matching-block and finite-period obstruction

**Established in Lean 4.36.0-rc2.** Every finite strictly interior signed path with a period of length k and N >= 2k steps satisfies `16^(N-2k) < p_N`. More generally, two exact signed paths sharing N consecutive digits at positive initial rank gap L and ending below rank P, with `P < 16^t`, satisfy, for every depth h,

    B = 4^h * (floor(L/(3*16^h)) + 1)
    N < max(t+h+B, 2*t+3*B).

A square of half-length k in a strict-interior path consequently satisfies `29*k < 64*t+6144` whenever its terminal rank is below `16^t`. The full q0 reduction forces a path of length 8u+5 starting at (24u+22,6u+4), of rank at most 72u+52. If `72u+52 < 16^t`, the square bound holds at every position on that forced path. This is a genuine all-parameter structural restriction, not an all-parameter exclusion: arbitrary aperiodic paths may avoid long squares.

## Proof mechanism

The signed graph is the exact four-digit model from [Q0MacroReduction](Q0MacroReduction.md): `p' = p+cost(d)`, `16*y' = y+d*p+offset(d)`, with `d in {0,1,4,5}` and `0 < 3*y < p` (and y positive). The argument uses the prior [aperiodicity and reverse-uniqueness theorem](Q0Aperiodic.md).

### Finite periodic segments

For a length-N itinerary with period k, the rank difference `p_(i+k)-p_i` is the constant L. Let `f_i = y_(i+k)-y_i`. Then `16*f_(i+1)=f_i+d_i*L`. Suppose `f_k=f_0`. The first k difference steps close a cycle, whose periodic extension obeys `0 <= 3*f_i <= L`: the inequalities `f_i <= 16*f_(i+1)` and `L-3*f_i <= 16*(L-3*f_(i+1))` cannot have a negative value on a periodic integer sequence. Thus the original block extends indefinitely by setting the rank and height at position `q*k+r` to `p_r+q*L` and `y_r+q*f_r`. Both exact step equations hold, and the strict interior is preserved. This would contradict `no_periodic_interior`.

Therefore the second difference `e_0=f_k-f_0` is nonzero. It obeys `e_i=16*e_(i+1)` for i < N-2k. Hence `16^(N-2k)` divides the nonzero integer e_0, whose absolute value is strictly less than terminal rank p_N, by strict interior and rank monotonicity. This proves the finite-period inequality even for nonprimitive periods and a partial final copy.

### Arbitrary-depth difference packing

Two paths sharing N digits retain their positive rank gap L. Their signed height difference f has the same homogeneous recurrence above. Both `f_0` and `L-3*f_0` exceed -P. The two quantities satisfy `g_i <= 16*g_(i+1)`, so after t steps, `P < 16^t` forces them to be nonnegative integers. Consequently the height differences thereafter are integer slopes in [0,L/3].

For any h-step slope history from a to b, `16^h*b=a+L*D`, where D is a base-16 word with digits 0,1,4,5. Since `0<=3*a<=L`, each D admits at most `floor(L/(3*16^h))+1` distinct integer endpoints. There are exactly 4^h words; the union therefore contains at most B integer slopes.

If `N >= t+h+B`, the last B+1 slopes each have an h-step interior history. Two must agree at indices i<j, with gap r=j-i<=B and j>=N-B+1. Reverse uniqueness for closed-interval slopes propagates their equality backwards to t, forcing the original digit segment from t to j to have period r. The finite-period bound (or the trivial length <2r case) gives `j-t < 2*r+t`. Combining the bounds yields `N < 2*t+3*B`. The shorter case gives the other term in the maximum.

For a square the two matching blocks have initial rank gap `L <= 6*k`. Taking h=3 gives `B=64*(floor(L/12288)+1)` and `32*B <= k+2048`. The second term of the maximum dominates, so `k < 2*t+3*B`, yielding the stated `29*k < 64*t+6144`. Optimizing h instead gives a paper-level asymptotic bound `k <= 2*t+O(sqrt(t))`: the band count is O(sqrt(L)) by choosing 4^h comparable to sqrt(L), and L<=6k. The exact arbitrary-depth inequality is the kernel-checked statement.

## Source and reproducibility

The three new modules are [Q0DifferencePacking.lean](Q0DifferencePacking.lean), [Q0FinitePeriod.lean](Q0FinitePeriod.lean) and [Q0CommonBlock.lean](Q0CommonBlock.lean). Their complete repository dependency closure was compiled locally, with byte-matched original files `Q0MacroCore.lean` (Git blob `06821faeb7c97a2b6f65adb68cdc2f707dcfa03e`), `Q0SlopePacking.lean` (`d5555857a991000209e9bab797c33b3ab801170d`) and `Q0Aperiodic.lean` (`679d6b2aa53641bfc7e485be9b9739c4582fafc7`). Lean 4.36.0-rc2 reports only standard `[propext, Classical.choice, Quot.sound]` for `deep_slope_packing`, `unequal_block_increments`, `finite_period_bound`, `common_block_bound`, `square_bound` and `q0_word_constraint`. No sorry or native_decide. Reproduce from this directory with `LEAN_PATH=.` and compile these six modules in dependency order with `lean -o NAME.olean NAME.lean`. The original raw-machine bridge is not recompiled here; `q0_word_constraint` uses the exact `Source` interface and `q0_path` theorem from Q0MacroCore.

## Remaining mathematical gap

This rules out long repeated blocks in any candidate, beyond the earlier whole-period and repeated-primitive-word results. It does not establish a bound on all paths from the q0 ray: long square-free or more generally aperiodic itineraries remain compatible with this necessary condition. A successful next step must relate the arithmetic of the initial ray and the required length 8u+5 to a forced forbidden pattern or a different global descent. Do not infer original #429 nonhalting or an improved BB(6) bound from this theorem alone.
