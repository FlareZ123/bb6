import SourceRawHalt38
import BB429NineSector
import Lean.Elab.Tactic.Omega
namespace BB429ActualNineSector
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA
/-- Genuine original Cryptids blank-root terminal, within the 9(mod128)
    sector, has first counter 9 or 649 modulo1024. -/
theorem source_nine_sector_two_classes (n u w : Nat)
    (hr : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hn : highLevelNext (.J u w) = none)
    (h9 : u%128=9) : u%1024=9 ∨ u%1024=649 := by
  have hl : BB429.run n (0,0)=some (u,w) :=
    BB429SourceMod16.source_run_to_local n u w hr
  have hg : w+1=2*u :=
    (BB429.next_none_iff_halt_line u w).mp
      (BB429SourceMod16.source_next_none_to_local u w hn)
  exact BB429NineSector.blank_terminal_nine_only_two n u w hl hg h9
#print axioms source_nine_sector_two_classes
end BB429ActualNineSector
