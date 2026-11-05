import SourceRawHalt38
import SourceRawHalt86
import BB429New34

namespace BB429ActualHalt40
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- Transport the source-certified 34 all-natural accelerated-root
    obstructions to the unchanged pinned original Cryptids high-level
    section. -/
theorem source_halt_not_new34 (n u w : Nat)
    (hr : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none) :
    ¬ BB429New34.NewGate u := by
  have hl : BB429.run n (0,0)=some (u,w) :=
    BB429SourceMod16.source_run_to_local n u w hr
  have hg : w+1=2*u :=
    (BB429.next_none_iff_halt_line u w).mp
      (BB429SourceMod16.source_next_none_to_local u w hn)
  exact BB429New34.blank_halt_not_newGate n u w hl hg

/-- Native original raw halting iff an actual high-level source exit
    belongs to the previously verified 38-mod-1024 gate filter,
    avoids Agent1's 1661 and 893 modulo 2048,
    and avoids all 34 newly source-proved entire 2048 residue rays.
    There are exactly 40 candidate residue classes modulo 2048
    under this conjunction; none is assumed reachable. -/
theorem raw_halts_iff_40_gates :
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
        ¬ BB429New34.NewGate u := by
  constructor
  · intro h
    obtain ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,h137,h521⟩ :=
      BB429ActualHalt38.raw_halts_iff_38_gates.mp h
    exact ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,h137,h521,
      BB429ActualHalt86.source_halt_not_1661_mod2048 n u w hr hn,
      BB429ActualHalt86.source_halt_not_893_mod2048 n u w hr hn,
      source_halt_not_new34 n u w hr hn⟩
  · rintro ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,h137,h521,
      h1661,h893,hnew⟩
    apply BB429ActualHalt38.raw_halts_iff_38_gates.mpr
    exact ⟨n,u,w,hr,hn,hmask,h253,h381,h509,h393,h265,h137,h521⟩

#print axioms source_halt_not_new34
#print axioms raw_halts_iff_40_gates
end BB429ActualHalt40
