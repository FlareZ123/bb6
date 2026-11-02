import DAllStarts
namespace BB6.Portfolio

theorem translate_haltsAt_iff (M : Machine) (delta : Int) (c : Cfg)
    (n : Nat) :
    HaltsAtCfg M (translateCfg delta c) n ↔ HaltsAtCfg M c n := by
  constructor
  · intro hh
    have ht := translate_haltsAt_forward M (-delta) (translateCfg delta c) n hh
    simpa only [translate_roundtrip] using ht
  · exact translate_haltsAt_forward M delta c n

theorem haltsAt_F0Pure_shift (M : Machine) (n : Nat) (h : Int) (t : Nat) :
    HaltsAtCfg M (F0Pure n h) t ↔ HaltsAtCfg M (F0Pure n 0) t := by
  have htrans := translate_haltsAt_iff M (-h) (F0Pure n h) t
  rw [translate_F0Pure] at htrans
  have heq : h+ -h=0 := by omega
  rw [heq] at htrans
  exact htrans.symm

/-- Every designated initial state has an exact primitive-step offset into
    one of four fully specified unary sections. -/
theorem all_blank_haltsAt_iff_unary (s : State) (n : Nat) :
    haltsAt D0 s (startTime s+n) ↔
      HaltsAtCfg D0 (F0Pure (startSeed s) 0) n := by
  exact (haltsAt_after_prefix D0 (blank s)
    (F0Pure (startSeed s) (startHead s)) (startTime s) n
      (every_blank_reaches_unary s)).trans
    (haltsAt_F0Pure_shift D0 (startSeed s) (startHead s) n)

/-- Original rooted RLE D1, D2, D3 share the source table D0, after exact
    reflection and state relabeling. The following are all-time *step-exact*
    iff statements, and should never be interpreted as halting decisions. -/
theorem D3_haltsAt_iff_I5 (n : Nat) :
    haltsAt D3 (0:State) (15+n) ↔ HaltsAtCfg D0 (F0Pure 5 0) n := by
  have h := D3_exact_halt_time (15+n)
  exact h.trans (by simpa [startTime,startSeed] using
    (all_blank_haltsAt_iff_unary (1:State) n))

theorem D2_haltsAt_iff_I15 (n : Nat) :
    haltsAt D2 (0:State) (92+n) ↔ HaltsAtCfg D0 (F0Pure 15 0) n := by
  have h := D2_exact_halt_time (92+n)
  exact h.trans (by simpa [startTime,startSeed] using
    (all_blank_haltsAt_iff_unary (2:State) n))

theorem D1_haltsAt_iff_I39 (n : Nat) :
    haltsAt D1 (0:State) (403+n) ↔ HaltsAtCfg D0 (F0Pure 39 0) n := by
  have h := D1_exact_halt_time (403+n)
  exact h.trans (by simpa [startTime,startSeed] using
    (all_blank_haltsAt_iff_unary (5:State) n))

#print axioms all_blank_haltsAt_iff_unary
#print axioms D3_haltsAt_iff_I5
#print axioms D2_haltsAt_iff_I15
#print axioms D1_haltsAt_iff_I39
end BB6.Portfolio
