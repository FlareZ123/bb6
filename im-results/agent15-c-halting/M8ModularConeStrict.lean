import M8SharpFamily
import ModularConeHighStop
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent15Research
open BB6.Agent29Depth
open BB6.Agent42ModularCone

theorem m8SharpJ_ge_two_for_cone (r : Nat) (hr : 2≤r) : 2 ≤ m8SharpJ r := by
  have hv8 := m8SharpV_mod_eight r hr
  have hv : 2≤m8SharpV r := by omega
  have hp : 1≤2^(m8SharpT r) := Nat.pow_pos (by decide)
  have hmul : 2≤m8SharpV r*2^(m8SharpT r) := Nat.mul_le_mul hv hp
  have h3 : 6≤3*m8SharpV r*2^(m8SharpT r) := by
    have h := Nat.mul_le_mul_left 3 hmul
    simpa [Nat.mul_assoc] using h
  dsimp [m8SharpJ]
  omega

theorem m8SharpM_ge_21_for_cone (r : Nat) (hr : 3≤r) : 21≤m8Geom4 r := by
  have ha := m8Geom4_three r
  have hp : 64 ≤ 4^r := Nat.pow_le_pow_right (by decide : 0 < (4:Nat)) hr
  omega

theorem m8SharpL_pow32_dvd_for_cone (r : Nat) (hr : 3≤r) :
    2^32 ∣ 4^(m8SharpL r) := by
  have hm : 21≤m8SharpM r := by
    simpa [m8SharpM] using m8SharpM_ge_21_for_cone r hr
  have hL : 16≤m8SharpL r := by
    dsimp [m8SharpL]
    omega
  obtain ⟨e,he⟩ : ∃e,2*m8SharpL r=32+e :=
    ⟨2*m8SharpL r-32,by omega⟩
  refine ⟨2^e,?_⟩
  rw [← m8PowTwoDouble, he, Nat.pow_add]

/-- Unified high parameter U=j+1 is congruent to -4^r-1 mod 2^32. -/
theorem m8SharpU_cong32 (r : Nat) (hr : 3≤r) :
    Cong 32 ((m8SharpJ r+1 : Nat) : Int) (-((4^r : Nat):Int)-1) := by
  have hr2 : 2≤r := by omega
  have hmain := m8SharpMain r hr2
  have hp2 : 2 ≤ 3*m8SharpV r*2^(m8SharpT r) := by
    have hv8 := m8SharpV_mod_eight r hr2
    have hv : 2 ≤ m8SharpV r := by omega
    have hp : 1 ≤ 2^(m8SharpT r) := Nat.pow_pos (by decide)
    have hmul : 2 ≤ m8SharpV r*2^(m8SharpT r) := Nat.mul_le_mul hv hp
    have h6 : 6 ≤ 3*(m8SharpV r*2^(m8SharpT r)) :=
      Nat.mul_le_mul_left 3 hmul
    have h6' : 6 ≤ 3*m8SharpV r*2^(m8SharpT r) := by
      simpa [Nat.mul_assoc] using h6
    omega
  have hj2 : m8SharpJ r+2 = 3*m8SharpV r*2^(m8SharpT r) := by
    dsimp [m8SharpJ]
    exact Nat.sub_add_cancel hp2
  have heq : m8SharpJ r+1+4^r+1=4^(m8SharpL r) := by
    calc
      m8SharpJ r+1+4^r+1 = (m8SharpJ r+2)+4^r := by omega
      _ = 3*m8SharpV r*2^(m8SharpT r)+4^r := by rw [hj2]
      _ = 4^(m8SharpL r) := hmain
  rcases m8SharpL_pow32_dvd_for_cone r hr with ⟨c,hc⟩
  unfold Cong I P
  refine ⟨(c:Int),?_⟩
  have heqI := congrArg (fun z : Nat => (z:Int)) heq
  have hcI := congrArg (fun z : Nat => (z:Int)) hc
  simp at heqI hcI ⊢
  omega

theorem m8SharpStopResidue32 (r : Nat) (hr : 3≤r) :
    residue 32 (stopResidue (m8SharpJ r+1) (m8SharpM r)) =
      residue 32 ⟨-(2*((4^r:Nat):Int)+1), -2⟩ := by
  have hU := m8SharpU_cong32 r hr
  have hm3nat := m8Geom4_three r
  have hm3 : (3*(m8SharpM r:Int)) = ((4^r:Nat):Int)-1 := by
    dsimp [m8SharpM]
    have h := congrArg (fun z : Nat => (z:Int)) hm3nat
    simp at h
    omega
  have hx : Cong 32 (2*(((m8SharpJ r+1 : Nat):Int))+1)
      (-(2*((4^r:Nat):Int)+1)) := by
    have h := cong_add (cong_mul_const hU 2) (cong_refl 32 1)
    have he : 2*(-((4^r:Nat):Int)-1)+1 =
        -(2*((4^r:Nat):Int)+1) := by omega
    rw [he] at h
    exact h
  have h3m : Cong 32 (3*(m8SharpM r:Int))
      (((4^r:Nat):Int)-1) := by
    rw [hm3]
    exact cong_refl _ _
  have hsum0 := cong_add hU h3m
  have hsum := cong_add hsum0 (cong_refl 32 4)
  have hy0 := cong_mul_const hsum (-1)
  have hy : Cong 32
      (-((((m8SharpJ r+1 : Nat):Int))+3*(m8SharpM r:Int)+4)) (-2) := by
    have he1 :
        (-1)*((((m8SharpJ r+1 : Nat):Int))+3*(m8SharpM r:Int)+4) =
          -((((m8SharpJ r+1 : Nat):Int))+3*(m8SharpM r:Int)+4) := by omega
    have he2 :
        (-1)*((-((4^r:Nat):Int)-1)+(((4^r:Nat):Int)-1)+4) = -2 := by omega
    rw [he1,he2] at hy0
    exact hy0
  change Pair.mk
      ((2*(((m8SharpJ r+1 : Nat):Int))+1) % I 32)
      ((-((((m8SharpJ r+1 : Nat):Int))+3*(m8SharpM r:Int)+4)) % I 32) =
    Pair.mk ((-(2*((4^r:Nat):Int)+1)) % I 32) ((-2) % I 32)
  rw [cong_mod hx, cong_mod hy]

theorem m8SharpConeTail_false : excluded 32 ⟨-1,-2⟩ = false := by
  decide

theorem m8SharpConeFinite_false (r : Nat) (hr : 3≤r) (hr15 : r≤15) :
    excluded 32 ⟨-(2*((4^r:Nat):Int)+1),-2⟩ = false := by
  have hcases :
      r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 ∨ r=9 ∨ r=10 ∨
      r=11 ∨ r=12 ∨ r=13 ∨ r=14 ∨ r=15 := by omega
  rcases hcases with h|h|h|h|h|h|h|h|h|h|h|h|h <;>
    subst r <;> decide

theorem m8SharpTwoFour_cong32 (r : Nat) (hr : 16≤r) :
    Cong 32 (2*((4^r:Nat):Int)) 0 := by
  have hnat : 2^32 ∣ 2*4^r := by
    obtain ⟨e,he⟩ : ∃e,2*r+1=32+e :=
      ⟨2*r+1-32,by omega⟩
    refine ⟨2^e,?_⟩
    calc
      2*4^r = 2*2^(2*r) := by rw [m8PowTwoDouble]
      _ = 2^(2*r+1) := by rw [Nat.pow_succ]; ac_rfl
      _ = 2^(32+e) := by rw [he]
      _ = 2^32*2^e := by rw [Nat.pow_add]
  rcases hnat with ⟨c,hc⟩
  unfold Cong I P
  refine ⟨(c:Int),?_⟩
  have hcI := congrArg (fun z : Nat => (z:Int)) hc
  simp at hcI ⊢
  omega

theorem m8SharpTailResidue32 (r : Nat) (hr : 16≤r) :
    residue 32 ⟨-(2*((4^r:Nat):Int)+1),-2⟩ =
      residue 32 ⟨-1,-2⟩ := by
  have hpow := m8SharpTwoFour_cong32 r hr
  have hx0 := cong_add hpow (cong_refl 32 1)
  have hx := cong_mul_const hx0 (-1)
  have he : (-1)*(2*((4^r:Nat):Int)+1) =
      -(2*((4^r:Nat):Int)+1) := by omega
  rw [he] at hx
  change Pair.mk ((-(2*((4^r:Nat):Int)+1)) % I 32) ((-2) % I 32) =
    Pair.mk ((-1) % I 32) ((-2) % I 32)
  rw [cong_mod hx]
  simp

/-- Every r≥2 M8 sharp-family target survives Agent42's current adaptive
    modular high-stop cone. The finite cases are kernel-reduced and the
    r≥16 tail stabilizes to one residue pair modulo 2^32. -/
theorem m8Sharp_not_modular_cone (r : Nat) (hr : 2≤r) :
    highStopExcluded (m8SharpJ r+1) (m8SharpM r) = false := by
  by_cases h2 : r=2
  · subst r
    decide
  have hr3 : 3≤r := by omega
  have hm : 21≤m8SharpM r := by
    simpa [m8SharpM] using m8SharpM_ge_21_for_cone r hr3
  have hj : 2≤m8SharpJ r+1 := by
    have := m8SharpJ_ge_two_for_cone r (by omega)
    omega
  have hbits :
      highStopBits (m8SharpJ r+1) (m8SharpM r)=32 := by
    simp [highStopBits,hj]
    omega
  rw [highStopExcluded,hbits]
  have hres := m8SharpStopResidue32 r hr3
  change check 32 32
      (residue 32 (stopResidue (m8SharpJ r+1) (m8SharpM r))) = false
  rw [hres]
  change excluded 32 ⟨-(2*((4^r:Nat):Int)+1),-2⟩ = false
  by_cases h15 : r≤15
  · exact m8SharpConeFinite_false r hr3 h15
  · have hr16 : 16≤r := by omega
    change check 32 32
      (residue 32 ⟨-(2*((4^r:Nat):Int)+1),-2⟩) = false
    rw [m8SharpTailResidue32 r hr16]
    simpa [excluded] using m8SharpConeTail_false

/-- Strictness against the current adaptive modular cone: the checker accepts
    every sharp-family parameter as unresolved, but the original-source M8
    quotient theorem proves its exact Machine-C target unreachable. -/
theorem m8Sharp_strict_beyond_modular_cone (r : Nat) (hr : 2≤r) :
    BB6.Agent42ModularCone.highStopExcluded
        (m8SharpJ r+1) (m8SharpM r) = false ∧
    ¬ BB6.Agent15.CReach (2*m8SharpJ r+3) (m8SharpK r) :=
  ⟨m8Sharp_not_modular_cone r hr, m8SharpFamily_unreachable r hr⟩

#print axioms m8Sharp_not_modular_cone
#print axioms m8Sharp_strict_beyond_modular_cone
end BB6.Agent15Research
