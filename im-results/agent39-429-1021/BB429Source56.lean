import BB429Source58
import SourceRawHalt1021Eight
import BB429Count56
import Lean.Elab.Tactic.Omega

namespace BB429Source56
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- Original raw-machine terminal witnesses miss both complete 8192
residue classes not included in Agent33's inverse38 list. -/
theorem original_terminal_not_extra (n u w : Nat)
    (hr : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) :
    u%8192 ≠ 1021 ∧ u%8192 ≠ 3069 := by
  obtain ⟨h1021,_,h3069,_,h9213,_,h11261,_⟩ :=
    BB429ActualHalt1021Eight.source_halt_not_eight_1021 n u w hr hn
  constructor
  · intro hm
    have hs : u%16384=1021 ∨ u%16384=9213 := by omega
    rcases hs with h | h
    · exact h1021 h
    · exact h9213 h
  · intro hm
    have hs : u%16384=3069 ∨ u%16384=11261 := by omega
    rcases hs with h | h
    · exact h3069 h
    · exact h11261 h

/-- Exact original raw Turing machine halting equivalence, reduced to
56 possible modulo8192 halting-counter residue classes. Each existential
witness must be genuinely reached by the blank-origin Cryptids machine. -/
theorem raw_halts_iff_56_classes :
    IsHalt target ↔
      ∃ n u w,
        BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
        highLevelNext (.J u w) = none ∧
        u%8192 ∈ BB429Count56.live56 := by
  rw [BB429Source58.raw_halts_iff_58_classes]
  constructor
  · rintro ⟨n,u,w,hr,hn,hl⟩
    obtain ⟨h1021,h3069⟩ := original_terminal_not_extra n u w hr hn
    exact ⟨n,u,w,hr,hn,(BB429Count56.live56_iff u).mpr ⟨hl,h1021,h3069⟩⟩
  · rintro ⟨n,u,w,hr,hn,hl⟩
    exact ⟨n,u,w,hr,hn,((BB429Count56.live56_iff u).mp hl).1⟩

#print axioms original_terminal_not_extra
#print axioms raw_halts_iff_56_classes

end BB429Source56
