import BB429Source25Mod2048
import BB429No81mod512

namespace BB429ActualHalt24Mod2048
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- The independently source-checked 81(mod512) exclusion applies to any
    genuine terminal section of the original Cryptids six-state machine. -/
theorem source_halt_not_81 (n u w : Nat)
    (hr : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) :
    u % 512 ≠ 81 := by
  have hl : BB429.run n (0,0) = some (u,w) :=
    BB429SourceMod16.source_run_to_local n u w hr
  have hg : w+1=2*u :=
    (BB429.next_none_iff_halt_line u w).mp
      (BB429SourceMod16.source_next_none_to_local u w hn)
  exact BB429No81.blank_halt_not_81_mod512 n u w hl hg

/-- Joint original-source theorem combining Agent1's 25-gate necessary
    criterion with Agent6's independent all-time 81(mod512) exclusion.
    The remaining candidate set has 24 residues modulo 2048, as checked
    separately by BB429GateArithmetic24. No candidate is asserted reachable. -/
theorem raw_halts_iff_24_gates :
    IsHalt target ↔
      ∃ n u w,
        BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
        highLevelNext (.J u w) = none ∧
        (u%64=9 ∨ u%128=81 ∨ u%64=53 ∨
          (u%128=125 ∧ u%1024≠125)) ∧
        u%1024≠253 ∧ u%1024≠381 ∧ u%1024≠509 ∧
        u%512≠393 ∧ u%512≠265 ∧
        u%1024≠137 ∧ u%1024≠521 ∧
        u%2048≠1661 ∧ u%2048≠893 ∧
        ¬ BB429New49.NewGate u ∧ u%512≠81 := by
  constructor
  · intro h
    obtain ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,
      h137,h521,h1661,h893,h49⟩ :=
        BB429ActualHalt25Mod2048.raw_halts_iff_25_gates.mp h
    exact ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,
      h137,h521,h1661,h893,h49,source_halt_not_81 n u w hr hn⟩
  · rintro ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,
      h137,h521,h1661,h893,h49,h81⟩
    exact BB429ActualHalt25Mod2048.raw_halts_iff_25_gates.mpr
      ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,
       h137,h521,h1661,h893,h49⟩

#print axioms source_halt_not_81
#print axioms raw_halts_iff_24_gates
end BB429ActualHalt24Mod2048
