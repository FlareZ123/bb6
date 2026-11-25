# Agent 18 — decisive obstruction to the macro short-barrier conjecture

The uniform five-coefficient two-row rank-barrier conjecture is FALSE. At a=23, k=117, b=0 there is an exact strict-interior crossing. Set B=23*16^117, initial p=B-354, y=13*16^115. Three words of length 117: w=0^115 5 0, v=0^115 5 5, z=5^115 0 0. The center is (B,115*16^115); after v rank B+357 and height (B+357-B/256)/3; after z rank B+1053 and height (B+1024)/768.

Kernel proof in im-results/agent18-429-odd-macro/OddResetBarrierCounterexample.lean (commit 001412886277e8654c5d43b7409bccdcdd156911), theorem cross2_23_0_117 and barrier_23_117_false. Lean 4.36.0-rc2, standard axioms only; actual Q0RankBarrier and first namespace of Q0DoubleBarrier compiled. Independent exact integer replay also succeeded.

Earlier finite certificates unaffected. Do not claim all-scale short barrier for the five fixed coefficients. This does NOT refute the much longer window barrier, nor rule out replacing individual failed coefficients. Construction: past 0^s u, then 0^s, a short bridge to the small complement boundary, then a long run of fives. This provides a systematic route to adversarial constructions without massive searches. Redirect to long-window arguments or a uniform alternative covering chain. The new odd-reset macro reductions remain valid.
