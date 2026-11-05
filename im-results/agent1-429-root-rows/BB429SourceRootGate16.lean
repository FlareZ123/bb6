import BB429Source58
import BB429NewRootGate16

namespace BB429SourceRootGate16
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- Two additional true-root exclusions transported to the unchanged
    original six-state machine via the source-to-local correspondence. -/
theorem source_halt_excludes2 (n u w : Nat)
    (hr : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) :
    u%65536 ∉ BB429NewRootGate16.excluded2 := by
  intro hm
  have hl : BB429.run n (0,0)=some (u,w) :=
    BB429SourceMod16.source_run_to_local n u w hr
  have hg : w+1=2*u :=
    (BB429.next_none_iff_halt_line u w).mp
      (BB429SourceMod16.source_next_none_to_local u w hn)
  exact BB429NewRootGate16.blank_no_halt_two
    n u w (u%65536) hl hg rfl hm

/-- Exact raw-machine halting equivalence, keeping only genuine source
    terminals in Agent 33's old 58 candidate modulo-8192 classes, with
    the two additional genuinely unreachable 65536 terminal cylinders. -/
theorem raw_halts_iff_58_plus2 :
    IsHalt target ↔
      ∃ n u w,
        BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
        highLevelNext (.J u w) = none ∧
        u%8192 ∈ BB429Count58.live58 ∧
        u%65536 ∉ BB429NewRootGate16.excluded2 := by
  constructor
  · intro h
    obtain ⟨n,u,w,hr,hn,h58⟩ :=
      BB429Source58.raw_halts_iff_58_classes.mp h
    exact ⟨n,u,w,hr,hn,h58,source_halt_excludes2 n u w hr hn⟩
  · rintro ⟨n,u,w,hr,hn,h58,_⟩
    exact BB429Source58.raw_halts_iff_58_classes.mpr
      ⟨n,u,w,hr,hn,h58⟩

#print axioms source_halt_excludes2
#print axioms raw_halts_iff_58_plus2
end BB429SourceRootGate16
