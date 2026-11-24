import OddEvenNonPowerParentFan
import Lean.Elab.Tactic.Omega

/-!
# Odd-z second-generation parent cone

For the low stopping ray m=512z+67, z=1 (mod 16), this file isolates
its depth-two parent H.  The first edge H -> R_u is checked against the
complete original-section inverse.  More importantly, H's own blank-root
reachability is reduced exactly to its direct parent and odd-depth
high-bounce parents by the generic theorem in OddEvenNonPowerParentFan.
-/

namespace BB6.Agent3OddEvenFan
open BB6.Agent46

def oddZM (z : Nat) : Nat := 512*z+67

def oddZParam (z : Nat) : Nat :=
  2^(2*oddZM z-5)-(6*z+1)

def oddZSecondLeft (z : Nat) : Nat :=
  (173*oddZParam z+15)/4

def oddZSecondRight (z : Nat) : Nat :=
  (1875*oddZParam z+245)/8

def oddZRayLeft (z : Nat) : Nat :=
  180*oddZParam z+28

def oddZRayRight (z : Nat) : Nat :=
  166*oddZParam z+25

private theorem two_pow_ge_succ (n : Nat) : n+1≤2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
      calc
        n+1+1 ≤ 2^n+2^n := by omega
        _ = 2^(n+1) := by rw [Nat.pow_succ]; omega

private theorem oddZ_param_large (z : Nat) (hz : z%16=1) :
    6*z+1 ≤ 2^(2*oddZM z-5) := by
  have hzpos : 1≤z := by omega
  have hlin : z+1≤2^z := two_pow_ge_succ z
  have hexp : z+3≤2*oddZM z-5 := by
    unfold oddZM
    omega
  have hpow : 2^(z+3)≤2^(2*oddZM z-5) :=
    Nat.pow_le_pow_right (by omega) hexp
  have hpowid : 2^(z+3)=8*2^z := by
    rw [Nat.pow_add]
    rw [show (2:Nat)^3=8 by decide]
    omega
  rw [hpowid] at hpow
  omega

private theorem oddZ_param_sum (z : Nat) (hz : z%16=1) :
    oddZParam z+6*z+1=2^(2*oddZM z-5) := by
  unfold oddZParam
  exact Nat.sub_add_cancel (oddZ_param_large z hz)

theorem oddZ_param_mod16 (z : Nat) (hz : z%16=1) :
    oddZParam z%16=9 := by
  have hsum := oddZ_param_sum z hz
  have hexp : 4≤2*oddZM z-5 := by
    unfold oddZM
    omega
  have hdiv : 16∣2^(2*oddZM z-5) := by
    have h := Nat.pow_dvd_pow 2 hexp
    simpa using h
  have hpowmod : 2^(2*oddZM z-5)%16=0 :=
    Nat.mod_eq_zero_of_dvd hdiv
  have hsumod : (oddZParam z+6*z+1)%16=0 := by
    rw [hsum]
    exact hpowmod
  omega

private theorem oddZ_second_divisions (z : Nat) (hz : z%16=1) :
    4*((173*oddZParam z+15)/4)=173*oddZParam z+15 ∧
    8*((1875*oddZParam z+245)/8)=1875*oddZParam z+245 := by
  have hu := oddZ_param_mod16 z hz
  have hAmod : (173*oddZParam z+15)%4=0 := by omega
  have hKmod : (1875*oddZParam z+245)%8=0 := by omega
  constructor
  · have h := Nat.mod_add_div (173*oddZParam z+15) 4
    omega
  · have h := Nat.mod_add_div (1875*oddZParam z+245) 8
    omega

theorem oddZ_second_parity_size (z : Nat) (hz : z%16=1) :
    oddZSecondLeft z%2=1 ∧ oddZSecondRight z%2=0 ∧
    5<oddZSecondLeft z ∧ 6≤oddZSecondRight z := by
  have hu := oddZ_param_mod16 z hz
  have huge : 9≤oddZParam z := by
    have h := Nat.mod_le (oddZParam z) 16
    omega
  obtain ⟨hA,hK⟩ := oddZ_second_divisions z hz
  have hAmod8 : (173*oddZParam z+15)%8=4 := by omega
  have hKmod16 : (1875*oddZParam z+245)%16=0 := by omega
  constructor
  · unfold oddZSecondLeft
    omega
  constructor
  · unfold oddZSecondRight
    omega
  constructor
  · unfold oddZSecondLeft
    omega
  · unfold oddZSecondRight
    omega

private theorem oddZ_affine_mass_cost (u : Nat)
    (hA : 4*((173*u+15)/4)=173*u+15)
    (hK : 8*((1875*u+245)/8)=1875*u+245) :
    8*((173*u+15)/4+(1875*u+245)/8+1)=2221*u+283 ∧
    (173*u+15)/4+2*((1875*u+245)/8)=512*u+65 := by
  constructor <;> omega

theorem oddZ_second_mass_cost (z : Nat) (hz : z%16=1) :
    8*(oddZSecondLeft z+oddZSecondRight z+1)=
      2221*oddZParam z+283 ∧
    oddZSecondLeft z+2*oddZSecondRight z=
      512*oddZParam z+65 := by
  obtain ⟨hA,hK⟩ := oddZ_second_divisions z hz
  exact oddZ_affine_mass_cost (oddZParam z) hA hK

private theorem oddZ_G_lt_power (z : Nat) (hz : z%16=1) :
    2221*z+323 < 2^(2*oddZM z-8) := by
  have hzpos : 1≤z := by omega
  have hlin : z+1≤2^z := two_pow_ge_succ z
  have hcoeff : 2221*z+323 < 4096*(z+1) := by omega
  have hpowid : 4096*2^z=2^(z+12) := by
    rw [Nat.pow_add]
    rw [show (2:Nat)^12=4096 by decide]
    omega
  have hexp : z+12≤2*oddZM z-8 := by
    unfold oddZM
    omega
  have hpow : 2^(z+12)≤2^(2*oddZM z-8) :=
    Nat.pow_le_pow_right (by omega) hexp
  omega

theorem oddZ_second_mass_gap (z : Nat) (hz : z%16=1) :
    2^(2*oddZM z+3)<oddZSecondLeft z+oddZSecondRight z+1 ∧
    oddZSecondLeft z+oddZSecondRight z+1<2^(2*oddZM z+4) := by
  let P := 2^(2*oddZM z-8)
  let G := 2221*z+323
  have hu := oddZ_param_sum z hz
  have hGmod : G%4=0 := by
    dsimp [G]
    omega
  have hGdiv : 4*(G/4)=G := by
    have h := Nat.mod_add_div G 4
    omega
  have hPpow : 2^(2*oddZM z-5)=8*P := by
    dsimp [P]
    have hexp : 2*oddZM z-5=(2*oddZM z-8)+3 := by
      unfold oddZM
      omega
    rw [hexp,Nat.pow_add]
    rw [show (2:Nat)^3=8 by decide]
    omega
  have hN : 2221*oddZParam z+283+6*G =
      2221*2^(2*oddZM z-5) := by
    rw [← hu]
    dsimp [G]
    omega
  have hmass8 := (oddZ_second_mass_cost z hz).1
  have hmassPlus :
      oddZSecondLeft z+oddZSecondRight z+1+3*(G/4)=2221*P := by
    dsimp [P]
    rw [hPpow] at hN
    omega
  have hGlt : G<P := by
    have h := oddZ_G_lt_power z hz
    dsimp [P,G] at *
    omega
  have hGpos : 0<G := by
    dsimp [G]
    omega
  have hG4pos : 0<G/4 := by omega
  have hG4le : G/4≤G := Nat.div_le_self G 4
  have htermpos : 0<3*(G/4) := by omega
  have htermlt : 3*(G/4)<3*P := by omega
  have hSlo :
      2218*P<oddZSecondLeft z+oddZSecondRight z+1 := by omega
  have hShi :
      oddZSecondLeft z+oddZSecondRight z+1<2221*P := by omega
  have hPowLo : 2048*P=2^(2*oddZM z+3) := by
    dsimp [P]
    have hexp : 2*oddZM z+3=(2*oddZM z-8)+11 := by
      unfold oddZM
      omega
    rw [hexp,Nat.pow_add]
    rw [show (2:Nat)^11=2048 by decide]
    omega
  have hPowHi : 4096*P=2^(2*oddZM z+4) := by
    dsimp [P]
    have hexp : 2*oddZM z+4=(2*oddZM z-8)+12 := by
      unfold oddZM
      omega
    rw [hexp,Nat.pow_add]
    rw [show (2:Nat)^12=4096 by decide]
    omega
  constructor <;> omega

theorem oddZ_second_mass_not_power (z : Nat) (hz : z%16=1) :
    ∀ n : Nat,
      oddZSecondLeft z+oddZSecondRight z+1≠2^n := by
  intro n hpow
  obtain ⟨hlo,hhi⟩ := oddZ_second_mass_gap z hz
  have hnlo : 2*oddZM z+3<n := by
    by_cases hle : n≤2*oddZM z+3
    · have hpowle : 2^n≤2^(2*oddZM z+3) :=
        Nat.pow_le_pow_right (by omega) hle
      omega
    · omega
  have hnhi : n<2*oddZM z+4 := by
    by_cases hle : 2*oddZM z+4≤n
    · have hpowle : 2^(2*oddZM z+4)≤2^n :=
        Nat.pow_le_pow_right (by omega) hle
      omega
    · omega
  omega

/-- The depth-two odd-z parent really is a source predecessor of R_u. -/
theorem oddZ_second_parent_edge (z : Nat) (hz : z%16=1) :
    secNext (oddZSecondLeft z,oddZSecondRight z)=
      some (oddZRayLeft z,oddZRayRight z) := by
  have hu := oddZ_param_mod16 z hz
  have hlarge := oddZ_second_parity_size z hz
  rcases hlarge with ⟨hAodd,hKeven,hAgt,hKge⟩
  obtain ⟨hA,hK⟩ := oddZ_second_divisions z hz
  have hRleft : 5<oddZRayLeft z := by
    unfold oddZRayLeft
    have huge : 9≤oddZParam z := by
      have h := Nat.mod_le (oddZParam z) 16
      omega
    omega
  have hRright : 6≤oddZRayRight z := by
    unfold oddZRayRight
    have huge : 9≤oddZParam z := by
      have h := Nat.mod_le (oddZParam z) 16
      omega
    omega
  have hmass :
      oddZRayLeft z+oddZRayRight z+1=
        8*(oddZSecondLeft z+3) := by
    change 180*oddZParam z+28+166*oddZParam z+25+1=
      8*((173*oddZParam z+15)/4+3)
    omega
  have hcost :
      2*oddZSecondRight z+oddZSecondLeft z+13=
        oddZRayLeft z+2*oddZRayRight z := by
    change 2*((1875*oddZParam z+245)/8)+
        (173*oddZParam z+15)/4+13=
      180*oddZParam z+28+2*(166*oddZParam z+25)
    omega
  have ha0 : oddZSecondLeft z≠0 := by omega
  have ha1 : oddZSecondLeft z≠1 := by omega
  have hk0 : oddZSecondRight z≠0 := by omega
  have hhigh : ¬ 2*oddZSecondRight z≤oddZSecondLeft z := by
    omega
  have hae : ¬ oddZSecondLeft z%2=0 := by omega
  have hpow :
      oddZRayLeft z+oddZRayRight z+1=
        2^2*(2*(oddZSecondLeft z-1)+8) := by
    calc
      oddZRayLeft z+oddZRayRight z+1 =
          8*(oddZSecondLeft z+3) := hmass
      _ = 4*(2*(oddZSecondLeft z+3)) := by omega
      _ = 4*(2*(oddZSecondLeft z-1)+8) := by omega
      _ = 2^2*(2*(oddZSecondLeft z-1)+8) := by
        rw [show (4:Nat)=2^2 by decide]
  have hcost' :
      (2*oddZSecondRight z-oddZSecondLeft z+3)+
        (2*(oddZSecondLeft z-1)+8)+3*2=
          oddZRayLeft z+2*oddZRayRight z+2 := by
    omega
  have hp : sectionPreimageCriterion
      (oddZSecondLeft z) (oddZSecondRight z)
      (oddZRayLeft z) (oddZRayRight z) := by
    simp only [sectionPreimageCriterion,if_neg ha0,if_neg ha1,
      if_neg hk0,if_neg hhigh,if_neg hae]
    exact ⟨2,hpow,hcost'⟩
  exact (complete_section_inverse
    (oddZSecondLeft z) (oddZSecondRight z)
    (oddZRayLeft z) (oddZRayRight z) (by omega)).mpr hp

/-- H's exact blank-root reachability decomposition: the generic
    direct-parent branch and the complete odd-depth high-bounce fan. -/
theorem oddZ_second_parent_reach_iff (z : Nat) (hz : z%16=1) :
    (∃ t, BB6.Agent8Section.run secNext t (some (5,1))=
      some (oddZSecondLeft z,oddZSecondRight z)) ↔
    (∃ t, BB6.Agent8Section.run secNext t (some (5,1))=
      some (oddZSecondLeft z+oddZSecondRight z-2,
        (oddZSecondRight z-2)/2)) ∨
    (∃ n a k t, n%2=1 ∧ a%2=1 ∧ 3≤a ∧ a<2*k ∧
      oddZSecondLeft z+oddZSecondRight z+1=2^(n+1)*(a+3) ∧
      2*k+a+7+3*n=oddZSecondLeft z+2*oddZSecondRight z ∧
      BB6.Agent8Section.run secNext t (some (5,1))=some (a,k)) := by
  have hsize := oddZ_second_parity_size z hz
  have hnp := oddZ_second_mass_not_power z hz
  rcases hsize with ⟨hodd,heven,hx,hy⟩
  exact blank_reach_iff_odd_even_nonpower_parent_fan
    (oddZSecondLeft z) (oddZSecondRight z) hx hodd hy heven hnp

#print axioms oddZ_second_parent_edge
#print axioms oddZ_second_mass_not_power
#print axioms oddZ_second_parent_reach_iff

end BB6.Agent3OddEvenFan
