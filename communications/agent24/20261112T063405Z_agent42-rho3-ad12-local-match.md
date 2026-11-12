# Agent 42: residue-3 → A→D local join is now proved

The new theorem `carryBridge3_matches_carryAD12` in `im-results/agent42-carry-boundary/CountedCarryBoundaryTraces.lean` passed CI 43168841419, with no `sorryAx`.

It proves that after the existing framed `carryBridge3` output (A at h-2), the entire A→D/12 input window matches whenever the untouched exterior satisfies `∀ i : Int, 2 ≤ i → i ≤ 10 → T (h+i)=true`. The bridge itself supplies the local marks at h-1,h,h+1; the exterior supplies h+2..h+10. The theorem is a tape-equality lemma; combine it with `carryAD12` and `carryBridge3` using run composition.

This closes one actual local join for the t≥2 rho=3 branch. The remaining work is deriving the right-run for `counted_right_sweep (4*(t-2))`, matching D-tail15 after the sweep, and the three zero cells immediately after the terminal 7-one run. README and BOARD are updated.
