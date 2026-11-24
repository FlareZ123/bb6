import ModularConeSource
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 4000000

namespace BB6.Agent42ModularCone

/-- Precision for the low stopping family j=0. The stopping equation
    supplies y+2 >= 3*2^(2*m+1). -/
def lowStopBits (m : Nat) : Nat := min 32 (2*m+1)

/-- Adaptive modular inverse-cone exclusion for the low stopping family. -/
def lowStopExcluded (m : Nat) : Bool :=
  excluded (lowStopBits m) (stopResidue 0 m)

/-- Fixed eight-bit low-stop cylinder predicate modulo 256. -/
def lowStopExcluded8 (m : Nat) : Bool :=
  excluded 8 (stopResidue 0 m)

theorem lowStopBits_bound (m : Nat) : lowStopBits m ≤ 2*m+1 :=
  Nat.min_le_right 32 (2*m+1)

/-- Every accepted adaptive low-stop cylinder is absent from the original
    Machine C source orbit. -/
theorem low_stop_excluded (m k : Nat)
    (hstop : k+3*m+4 = P (2*m+2)*2)
    (hc : lowStopExcluded m = true) :
    ¬ BB6.Agent3.CReach 1 k := by
  let b := lowStopBits m
  have hb : b ≤ 2*m+1 := lowStopBits_bound m
  have hcheck : excluded b (stopResidue 0 m) = true := by
    simpa [lowStopExcluded,b] using hc
  have hstop' : k+0+3*m+4 = P (2*m+2)*(0+2) := by
    simpa using hstop
  exact source_stop_cylinder_excluded b 0 m 0 m k
    (Or.inl hb) (cong_refl b (0:Int)) (cong_refl b (m:Int)) hstop' hcheck

/-- Fixed eight-bit version: every accepted residue modulo 256 excludes
    the compatible low-stop target for all m>=4. -/
theorem low_stop_excluded8 (m k : Nat) (hm : 4 ≤ m)
    (hstop : k+3*m+4 = P (2*m+2)*2)
    (hc : lowStopExcluded8 m = true) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hstop' : k+0+3*m+4 = P (2*m+2)*(0+2) := by
    simpa using hstop
  exact source_stop_cylinder_excluded 8 0 m 0 m k
    (Or.inl (by omega))
    (cong_refl 8 (0:Int)) (cong_refl 8 (m:Int)) hstop'
    (by simpa [lowStopExcluded8] using hc)

/-- Concrete non-immediate low-stop exclusion. The root residue is (1,219)
    modulo 256, so it is not in the immediate odd-image forbidden set. -/
theorem low_stop_example_11 :
    ¬ BB6.Agent3.CReach 1 33554395 := by
  have hc : lowStopExcluded8 11 = true := by decide
  have hs : 33554395+3*11+4 = P (2*11+2)*2 := by decide
  exact low_stop_excluded8 11 33554395 (by omega) hs hc

#print axioms low_stop_excluded
#print axioms low_stop_excluded8
#print axioms low_stop_example_11

end BB6.Agent42ModularCone
