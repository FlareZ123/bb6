import BusyBeaver.BB6.M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB
import SProjection

namespace Agent9SourceSProjection
open BusyBeaver.M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB
open Agent9SProjection

def projectS : Option HighLevelState → Option (Nat × Nat)
  | some (.S b c) => some (b+16,c)
  | _ => none

theorem projection_exact (b c : Nat) :
    projectS (highLevelNext (.S b c)) = Sstep (b+16) c := by
  unfold projectS Sstep highLevelNext
  by_cases h0 : b % 3 = 0
  · have hq : (b+16)%3=1 := by omega
    simp [h0,hq]
    congr 1
    omega
  · by_cases h1 : b%3=1
    · have hq0 : (b+16)%3 ≠ 0 := by omega
      have hq1 : (b+16)%3 ≠ 1 := by omega
      simp [h0,h1,hq0,hq1]
      congr 1
      omega
    · have hq : (b+16)%3=0 := by omega
      by_cases hc : c = 0
      · simp [h0,h1,hq,hc]
      · simp [h0,h1,hq,hc]
        congr 1
        omega

#print axioms projection_exact
end Agent9SourceSProjection
