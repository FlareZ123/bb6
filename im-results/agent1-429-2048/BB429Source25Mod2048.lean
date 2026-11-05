import BB429Source40Mod2048
import BB429New49

namespace BB429ActualHalt25Mod2048
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- Exact transport of forty-nine all-natural accelerated blank-root
    terminal-ray exclusions into the original pinned Google DeepMind
    Cryptids target machine. -/
theorem source_halt_not_new49 (n u w : Nat)
    (hr : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) :
    ¬ BB429New49.NewGate u := by
  have hl : BB429.run n (0,0)=some (u,w) :=
    BB429SourceMod16.source_run_to_local n u w hr
  have hg : w+1=2*u :=
    (BB429.next_none_iff_halt_line u w).mp
      (BB429SourceMod16.source_next_none_to_local u w hn)
  exact BB429New49.blank_halt_not_newGate n u w hl hg

/-- For the original raw six-state two-symbol machine, real halting
    is equivalent to reaching an actual terminal high-level section
    satisfying the previous root 38/1024 masks, two older 2048
    exclusions, and forty-nine new complete residue exclusions.
    The logical filter has exactly 25 surviving classes modulo 2048;
    this count is separately checked in BB429GateArithmetic25.lean.
    None of those 25 classes has been shown reachable. -/
theorem raw_halts_iff_25_gates :
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
        ¬ BB429New49.NewGate u := by
  constructor
  · intro h
    obtain ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,h137,h521,
      h1661,h893,h34⟩ :=
      BB429ActualHalt40Mod2048.raw_halts_iff_40_gates.mp h
    exact ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,h137,h521,
      h1661,h893,source_halt_not_new49 n u w hr hn⟩
  · rintro ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,h137,h521,
      h1661,h893,h49⟩
    have h34 : ¬ BB429New34.NewGate u := by
      intro h
      exact h49 (show BB429New49.NewGate u from Or.inl h)
    apply BB429ActualHalt40Mod2048.raw_halts_iff_40_gates.mpr
    exact ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,h137,h521,
      h1661,h893,h34⟩

#print axioms source_halt_not_new49
#print axioms raw_halts_iff_25_gates
end BB429ActualHalt25Mod2048
