import BB429Source52
import SourceRawHaltManyLifts
import SourceRawHaltFiveShift
import BB429Count58Sixteen

namespace BB429Source58Sixteen
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- Exact necessary first-counter residue set of size 58 modulo 16384
    for the original Google DeepMind Cryptids six-state raw machine. -/
theorem raw_halts_iff_58_classes_mod16384 :
    IsHalt target ↔
      ∃ n u w,
        BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
        highLevelNext (.J u w) = none ∧
        u%16384 ∈ BB429Count58Sixteen.live58 := by
  rw [BB429Source52.raw_halts_iff_52_classes]
  constructor
  · rintro ⟨n,u,w,hr,hn,hl⟩
    have h40 := BB429ActualManyLifts.source_halt_not_new_lifts n u w hr hn
    have h11473 := BB429ActualHalt16384.source_no_11473_mod16384 n u w hr hn
    have h5 := BB429ActualFiveShift.source_halt_not_five n u w hr hn
    exact ⟨n,u,w,hr,hn,
      (BB429Count58Sixteen.live58_iff u).mpr ⟨hl,h40,h11473,h5⟩⟩
  · rintro ⟨n,u,w,hr,hn,hl⟩
    exact ⟨n,u,w,hr,hn,((BB429Count58Sixteen.live58_iff u).mp hl).1⟩

#print axioms raw_halts_iff_58_classes_mod16384
end BB429Source58Sixteen
