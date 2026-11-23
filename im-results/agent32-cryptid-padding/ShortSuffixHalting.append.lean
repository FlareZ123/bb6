/- New source-level halting feeder: every unary length 3*k+4 with the
   indicated 12-bit suffix prefix has a terminal E boundary after the
   external step_An4_110100E reduction. The finite right-hand remainder is
   arbitrary. The terminal segment is 74 raw steps. -/
set_option maxHeartbeats 10000000 in
theorem halts_A_mod3_prefix_01100 (k : Nat) (ys : List Symbol) :
    halts tm (A (3*k+4) ([1,0,1,1,0,1,1,0,1,1,0,0] ++ ys)) := by
  apply stepStar_halts (step_An4_110100E k _)
  simp_rw [Turing.ListBlank.append]
  iterate 74 stepHalt
  exists 0
  simp_rw [haltsIn, stepNat, Nat.repeat, Option.some.injEq, exists_eq_left']
  rfl

#print axioms halts_A_mod3_prefix_01100
