import BB429Source56
import BB429FourSplit
import BB429Count52

namespace BB429Source52
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- Original pinned Cryptids high-level terminal implies the complete
    newly excluded genuine-root classes modulo 8192. -/
theorem source_halt_not_four (n u w : Nat)
    (hr : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) :
    u%8192≠201 ∧ u%8192≠209 ∧
    u%8192≠245 ∧ u%8192≠637 := by
  have hl : BB429.run n (0,0) = some (u,w) :=
    BB429SourceMod16.source_run_to_local n u w hr
  have hg : w+1=2*u :=
    (BB429.next_none_iff_halt_line u w).mp
      (BB429SourceMod16.source_next_none_to_local u w hn)
  exact BB429FourSplit.blank_halt_not_four n u w hl hg

/-- For the actual six-state two-symbol raw machine, halting is equivalent
    to existence of a *genuinely reached* terminal high-level configuration
    in one of 52 necessary first-counter classes modulo 8192.
    This is not an assertion that any class is reachable. -/
theorem raw_halts_iff_52_classes :
    IsHalt target ↔
      ∃ n u w,
        BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
        highLevelNext (.J u w) = none ∧
        u%8192 ∈ BB429Count52.live52 := by
  rw [BB429Source56.raw_halts_iff_56_classes]
  constructor
  · rintro ⟨n,u,w,hr,hn,hl⟩
    obtain ⟨h201,h209,h245,h637⟩ := source_halt_not_four n u w hr hn
    exact ⟨n,u,w,hr,hn,
      (BB429Count52.live52_iff u).mpr ⟨hl,h201,h209,h245,h637⟩⟩
  · rintro ⟨n,u,w,hr,hn,hl⟩
    exact ⟨n,u,w,hr,hn,((BB429Count52.live52_iff u).mp hl).1⟩

#print axioms source_halt_not_four
#print axioms raw_halts_iff_52_classes
end BB429Source52
