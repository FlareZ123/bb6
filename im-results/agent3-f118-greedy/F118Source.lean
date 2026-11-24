import BusyBeaver.BB6.M_1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_HHH1LC
import F118Greedy
namespace F118Source
open BusyBeaver
open BusyBeaver.M_1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_HHH1LC
local notation "Ueval" => BusyBeaver.M_1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_HHH1LC.evalK
local notation "Udrain" => BusyBeaver.M_1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_HHH1LC.drainD

def toHigh (p : Nat × Nat) : HighLevelState := .D p.1 p.2

theorem evalK_eq (k c : Nat) : Ueval k c = F118.evalK k c := by
  rw [BusyBeaver.M_1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_HHH1LC.evalK.eq_def,F118.evalK.eq_def]
  dsimp only
  split
  · exact evalK_eq _ _
  · rfl
termination_by k
decreasing_by omega

theorem drainD_eq (a d c : Nat) : Udrain a d c = (F118.drainD a d c).map toHigh := by
  rw [BusyBeaver.M_1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_HHH1LC.drainD.eq_def,F118.drainD.eq_def]
  split
  · split <;> rfl
  · dsimp only
    simp only [evalK_eq]
    exact drainD_eq _ _ _
termination_by a
decreasing_by omega

def newNext : HighLevelState → Option HighLevelState
  | .D a c => (F118.sectionNext (a,c)).map toHigh

theorem high_eq : highLevelNext = newNext := by
  funext s
  cases s with
  | D a c =>
    simp only [highLevelNext,newNext,drainD_eq,F118.section_eq]

theorem blank_halts_iff : IsHalt target ↔ CollatzHalts newNext (.D 0 1) := by
  rw [← high_eq, ← isHalt_iff_highLevel_acceleration]

#print axioms evalK_eq
#print axioms drainD_eq
#print axioms high_eq
#print axioms blank_halts_iff
end F118Source
