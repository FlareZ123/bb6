import DExactTimes

namespace BB6.Portfolio

/-- The two completely distinct original D0 blank starts in B and D
    meet in the identical complete physical configuration after 15 steps. -/
theorem blank_B_D_fuse (n : Nat) :
    run D0 (15+n) (some (blank (1:State))) =
    run D0 (15+n) (some (blank (3:State))) := by
  have hd : run D0 15 (some (blank (3:State))) =
      some (F0Pure 5 (-3)) := by
    have ht : startTime (3:State) = 15 := by decide
    have hn : startSeed (3:State) = 5 := by decide
    have hh : startHead (3:State) = -3 := by decide
    simpa only [ht,hn,hh] using (every_blank_reaches_unary (3:State))
  rw [run_add,run_add,blank_root_B_to_I5,hd]

/-- The original D0 blank starts in C and E have identical infinite
    futures after an exact one-step time offset and a physical tape shift. -/
theorem blank_C_E_shift_fuse (n : Nat) :
    run D0 (92+n) (some (blank (2:State))) =
      (run D0 (93+n) (some (blank (4:State)))).map (translateCfg 1) := by
  have he : run D0 93 (some (blank (4:State))) =
      some (F0Pure 15 (-13)) := by
    have ht : startTime (4:State) = 93 := by decide
    have hn : startSeed (4:State) = 15 := by decide
    have hh : startHead (4:State) = -13 := by decide
    simpa only [ht,hn,hh] using (every_blank_reaches_unary (4:State))
  rw [run_add,run_add,blank_root_C_to_I15,he]
  have hh : F0Pure 15 (-12) = translateCfg 1 (F0Pure 15 (-13)) := by
    simpa only [translate_F0Pure] using
      (Eq.symm (show translateCfg 1 (F0Pure 15 (-13)) = F0Pure 15 (-12) by
        simpa using (translate_F0Pure 15 (-13) 1)))
  rw [hh]
  exact (run_transport D0 D0 (translateCfg 1) (translate_step D0 1)
    n (some (F0Pure 15 (-13))))

/-- B and D share all primitive halting times after their 15-step prefixes. -/
theorem blank_B_D_same_exact_halt (n : Nat) :
    haltsAt D0 (1:State) (15+n) ↔ haltsAt D0 (3:State) (15+n) := by
  have hb := all_blank_haltsAt_iff_unary (1:State) n
  have hd := all_blank_haltsAt_iff_unary (3:State) n
  have htime1 : startTime (1:State)=15 := by decide
  have htime : startTime (3:State)=15 := by decide
  have hseed : startSeed (3:State)=5 := by decide
  simpa only [htime1,htime,hseed] using hb.trans hd.symm

/-- C and E's primitive halt times have an exact one-step offset. -/
theorem blank_C_E_same_exact_halt (n : Nat) :
    haltsAt D0 (2:State) (92+n) ↔ haltsAt D0 (4:State) (93+n) := by
  have hc := all_blank_haltsAt_iff_unary (2:State) n
  have he := all_blank_haltsAt_iff_unary (4:State) n
  have htime2 : startTime (2:State)=92 := by decide
  have htime : startTime (4:State)=93 := by decide
  have hseed : startSeed (4:State)=15 := by decide
  simpa only [htime2,htime,hseed] using hc.trans he.symm

#print axioms blank_B_D_fuse
#print axioms blank_C_E_shift_fuse
#print axioms blank_B_D_same_exact_halt
#print axioms blank_C_E_same_exact_halt
end BB6.Portfolio
