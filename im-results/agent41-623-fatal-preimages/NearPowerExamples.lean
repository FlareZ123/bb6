import NearPowerChecks
import NearPowerTreeSource
import FatalFamilyWindow

namespace BB6.Agent41NearPower
open BB6.Agent41FatalInverse BB6.Agent49ParitySource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

/-- Connect the compressed initial state to the exact family coordinates. -/
theorem fatalState_rep (k : Nat) (hk : 7≤k) : Represents (fatalState (k+1)) (targetX k) (targetY k) := by
  have hp := pow_margin k hk
  have hb := base_power k
  have ho := pow_three_odd (k+1)
  have hY := targetY_formula k hk
  have hp' : 3^(k+1)=3*3^k := by rw [Nat.pow_succ]; omega
  have hcast : ((3^(k+1):Nat):Int)=(3:Int)^(k+1) := Int.natCast_pow 3 (k+1)
  unfold Represents fatalState targetX
  simp only [Int.ofNat_one,Int.one_mul,Int.reduceNeg,Int.natCast_succ]
  rw [←hcast]
  omega

/-- A nontrivial reverse tree with depth 23 excludes every root index. -/
theorem excluded5288 (i : Nat) : run i≠some (.D (targetX 5287) (targetY 5287)) :=
  check_excludes cert5288 _ _ _ (fatalState_rep 5287 (by decide)) checked5288 i

/-- Even a target with exponent 10^100 can be excluded without constructing its counters. -/
theorem excludedHuge (i : Nat) : run i≠some (.D (targetX (10^100-1)) (targetY (10^100-1))) := by
  have h := fatalState_rep (10^100-1) (by decide +kernel)
  have he : 10^100-1+1=10^100 := by decide +kernel
  rw [he] at h
  exact check_excludes certHuge _ _ _ h checkedHuge i

#print axioms fatalState_rep
#print axioms checked5288
#print axioms checkedHuge
#print axioms excluded5288
#print axioms excludedHuge
end BB6.Agent41NearPower
