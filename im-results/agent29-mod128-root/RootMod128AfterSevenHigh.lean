import RootMod128High
import RootMod128Source
import OddSevenForcedRoot
import Lean.Elab.Tactic.Omega

namespace BB6.Agent29New

/-- Arithmetic transport of a full infinite original high-stopping
family through Agent19's old sum-seven forced direct-parent rule and
into the new source-root forbidden two-link cylinder. -/
theorem high_after_seven_coordinates (j m k : Nat)
    (hm : m%32=6) (hj : (j+51)%256=(9*m)%256)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    let x := 2*j+3
    let a := x+k-2
    let b := (k-2)/2
    k%8=6 ∧ (x+k+1)%32=16 ∧ (a%16=13) ∧
    (a+b+1)%128=96 ∧ 34≤b ∧ 48≤x+k+1 := by
  have hm6 : 6≤m := by omega
  have hpowdiv : 256 ∣ 2^(2*m+2) := by
    change 2^8 ∣ 2^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨q,hq⟩ := hpowdiv
  have hdiv : 256 ∣ k+j+3*m+5 := by
    refine ⟨q*(j+3), ?_⟩
    calc
      k+j+3*m+5 = 2^(2*m+2)*(j+3) := hgate
      _ = (256*q)*(j+3) := by rw [hq]
      _ = 256*(q*(j+3)) := by ac_rfl
  have hhmod : (k+j+3*m+5)%256=0 := Nat.mod_eq_zero_of_dvd hdiv
  have hlow : 4*m+4 ≤ 2^(2*m+2) := power_linear_bound m
  have hp1 : 1≤2^(2*m+2) := by omega
  have hmul : j ≤ 2^(2*m+2)*j := by
    have hh := Nat.mul_le_mul_right j hp1
    simpa using hh
  have hdist : 2^(2*m+2)*(j+3)=2^(2*m+2)*j+3*2^(2*m+2) := by
    simp [Nat.mul_add, Nat.mul_comm]
  have hlarge : 70≤k := by
    by_cases h6 : m=6
    · subst m
      have hp : (2:Nat)^(2*6+2)=16384 := by decide
      rw [hp] at hgate
      omega
    · have hm38 : 38≤m := by omega
      omega
  dsimp
  omega

theorem blank_no_high_after_seven (j m k : Nat)
    (hm : m%32=6) (hj : (j+51)%256=(9*m)%256)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  obtain ⟨hymod,hmod,hxparent,hsparent,hyparent,hbig⟩ :=
    high_after_seven_coordinates j m k hm hj hgate
  intro hr
  have hparent := (BB6.Agent19Seven.sumseven_forced_root_iff
    (2*j+3) k (by omega) hymod hmod hbig).mp hr
  exact (blank_no_two_link
    ((2*j+3)+k-2) ((k-2)/2) hxparent hsparent hyparent) hparent

#print axioms high_after_seven_coordinates
#print axioms blank_no_high_after_seven
end BB6.Agent29New
