import BB429Source58Sixteen
import SourceRawHaltSplit
import BB429SurvivorMask

namespace BB429Actual255
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

private theorem base58_matches_original :
    BB429SurvivorMask.base58 = BB429Count58Sixteen.live58 := by rfl

/-- Exact original raw-machine halting iff a genuinely reached high-level
    terminal belongs to the 255-class necessary gate modulo 262144. -/
theorem raw_halts_iff_255_classes_mod262144 :
    IsHalt target ↔
      ∃ n u w,
        BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
        highLevelNext (.J u w) = none ∧
        u%262144 ∈ BB429SurvivorMask.live255 := by
  rw [BB429Source58Sixteen.raw_halts_iff_58_classes_mod16384]
  constructor
  · rintro ⟨n,u,w,hr,hn,h58⟩
    have h673 := BB429ActualSplitSieve.source_halt_not_673 n u w hr hn
    have h58' : u%16384 ∈ BB429SurvivorMask.base58 := by
      rw [base58_matches_original]
      exact h58
    exact ⟨n,u,w,hr,hn,
      (BB429SurvivorMask.live255_iff u).mpr ⟨h58',h673⟩⟩
  · rintro ⟨n,u,w,hr,hn,h255⟩
    have h58' := ((BB429SurvivorMask.live255_iff u).mp h255).1
    have h58 : u%16384 ∈ BB429Count58Sixteen.live58 := by
      rw [← base58_matches_original]
      exact h58'
    exact ⟨n,u,w,hr,hn,h58⟩

#print axioms raw_halts_iff_255_classes_mod262144
end BB429Actual255
