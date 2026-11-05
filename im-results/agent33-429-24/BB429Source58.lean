import BB429Gate24Class
import BB429Inverse38
import BB429Count58

namespace BB429Source58
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

theorem source_halt_excludes38 (n u w : Nat)
    (hr : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) :
    u%8192 ∉ BB429Kernel.excluded38 := by
  intro hm
  have hl : BB429.run n (0,0)=some (u,w) :=
    BB429SourceMod16.source_run_to_local n u w hr
  have hg : w+1=2*u :=
    (BB429.next_none_iff_halt_line u w).mp
      (BB429SourceMod16.source_next_none_to_local u w hn)
  exact BB429Kernel.blank_no_halt_38 n u w (u%8192) hl hg rfl hm

theorem raw_halts_iff_58_constraints :
    IsHalt target ↔
      ∃ n u w,
        BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
        highLevelNext (.J u w) = none ∧
        u%2048 ∈ BB429Final24.liveClasses ∧
        u%8192 ∉ BB429Kernel.excluded38 := by
  constructor
  · intro h
    obtain ⟨n,u,w,hr,hn,hl⟩ := BB429Final24.raw_halts_iff_24_classes.mp h
    exact ⟨n,u,w,hr,hn,hl,source_halt_excludes38 n u w hr hn⟩
  · rintro ⟨n,u,w,hr,hn,hl,_⟩
    exact BB429Final24.raw_halts_iff_24_classes.mpr ⟨n,u,w,hr,hn,hl⟩

theorem live24_eq : BB429Final24.liveClasses = BB429Count58.live24 := by rfl
theorem excluded38_eq : BB429Kernel.excluded38 = BB429Count58.excluded38 := by rfl

/-- Original raw six-state machine halts iff a genuine reached terminal has
    its first counter in exactly one of the 58 remaining modulo-8192 classes.
    No listed class is thereby proved reachable. -/
theorem raw_halts_iff_58_classes :
    IsHalt target ↔
      ∃ n u w,
        BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
        highLevelNext (.J u w) = none ∧
        u%8192 ∈ BB429Count58.live58 := by
  rw [raw_halts_iff_58_constraints]
  constructor
  · rintro ⟨n,u,w,hr,hn,hl,he⟩
    have hgood : u%2048 ∈ BB429Count58.live24 ∧
      u%8192 ∉ BB429Count58.excluded38 := by
      simpa only [←live24_eq,←excluded38_eq] using And.intro hl he
    exact ⟨n,u,w,hr,hn,(BB429Count58.live58_iff u).mpr hgood⟩
  · rintro ⟨n,u,w,hr,hn,hl⟩
    have hgood := (BB429Count58.live58_iff u).mp hl
    have hgood' : u%2048 ∈ BB429Final24.liveClasses ∧
      u%8192 ∉ BB429Kernel.excluded38 := by
      simpa only [live24_eq,excluded38_eq] using hgood
    exact ⟨n,u,w,hr,hn,hgood'.1,hgood'.2⟩

#print axioms raw_halts_iff_58_classes
#print axioms source_halt_excludes38
#print axioms raw_halts_iff_58_constraints
end BB429Source58
