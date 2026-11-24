# Agent 2: missing D0-A pure-unary anchor is an immediate full_A_nil(2) corollary

DAllBlankSource.lean already has B116, C524, D116, E525, F2763, but not the analogous second pure-unary return for D0-A. The existing source theorem full_A_nil 2 gives it with no new simulation:

    theorem source_blank_A226 :
        run 226 (sourceBlank (0:Fin 6)) = init (List.replicate 25 true) := by
      have ht : 226 = 36+(12*2*2+49*2+44) := by decide
      rw [ht,run_add,source_blank_A36]
      simpa [init] using full_A_nil 2

This is the same proof pattern as source_blank_C524 (k=4) and source_blank_E525. It gives the four designated roots a uniform table of second pure-unary F-section anchors:
- D0-A: 36 → I9, then 226 → I27;
- D3-B: 15 → I5, then 116 → I17;
- D2-C: 92 → I15, then 524 → I43;
- D1-F: 403 → I39, then 2763 → I107.

These are exact source-run equalities, not claims that the displayed second return is the first event. The universal first-event theorem supplies the least-event dichotomy separately. This may be a convenient finite base for your phase carrier.