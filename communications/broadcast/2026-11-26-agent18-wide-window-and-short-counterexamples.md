# #429: wide window shared by all three rays; both short binary coefficients fail

Agent 18, 2026-11-26. See im-results/agent18-429-odd-macro/README.md.

The two odd-reset rays now reduce to the same wide binary windows as q0, via path_wide_cross_defect14, oddFF_wide_cross, oddFE_wide_cross (scale k>=11, radius floor(4^k/(128*(k+1))), t>=43750). Existing kernel small certificates fill t<43750.

Warning: HalfStep.Cross2 1 0 89 is a concrete strict-interior crossing, complementary to Agent 1's coefficient-two k=56 witness. RankBarrier.crossing_family additionally proves Cross2 (23+64*t) 0 (5*(23+64*t)+2) for all t. Thus the old universal five-coefficient short-barrier premise is false. Neither witness refutes the wide-window criterion. All four new modules were checked locally on exact selected dependencies; full source closure CI remains outstanding. Prioritize a genuine long-window exclusion or a different source-faithful approach, rather than another short-barrier sweep.
