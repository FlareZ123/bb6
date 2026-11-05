import SheepOddGap
import IndependentGenericHigh

namespace Sheep648RootHigh0

/-- Exact source-shaped h=0 generic inverse rules out all a>=2 for the
whole root j=648+122472k family. -/
theorem no_root_h0_high (k a v : Nat) (ha : 2 ≤ a)
    (heq : (2^(a+1)+1)*v + 2*a+2 = 2^(648+122472*k+1)+3) : False := by
  have hlin : (2^(a+1)+1)*v+(2*a-1)=2^(648+122472*k+1) := by omega
  have hbase :
      (1:Int)<SheepIndependentGenericHigh.K 1 (0:Int) a ∧
      SheepIndependentGenericHigh.K 1 (0:Int) a % 2=1 ∧
      SheepIndependentGenericHigh.K 1 (0:Int) a < (2:Int)^a ∧
      2*(1:Int) ≤ (2:Int)^a :=
    SheepIndependentGenericHigh.high_all 1 2 (0:Int) (by decide) a ha
  have hK : SheepIndependentGenericHigh.K 1 (0:Int) a=(2*a-1:Int) := by
    simp [SheepIndependentGenericHigh.K]
    omega
  rw [hK] at hbase
  rcases hbase with ⟨hlo,hodd,hhi,_⟩
  have hgap := (SheepOddGap.no_power_signed_small_odd a (2*a-1:Int)
    hlo hodd hhi (648+122472*k+1)).1
  have hcast : ((2:Int)^(a+1)+1)*(v:Int)+(2*a-1:Int) =
      (2:Int)^(648+122472*k+1) := by exact_mod_cast hlin
  have hdiv : ((2:Int)^(a+1)+1) ∣
      (2:Int)^(648+122472*k+1)-(2*a-1:Int) := by
    refine ⟨(v:Int),?_⟩
    omega
  exact hgap hdiv

#print axioms no_root_h0_high
end Sheep648RootHigh0
