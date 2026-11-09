import CThreeAltSource
import CThreeGenericStop
import Lean.Elab.Tactic.Omega

namespace BB6.Agent4Three
open BB6.Agent46

private theorem power_linear_alt (m : Nat) :
    4*m+4 ≤ (2:Nat)^(2*m+2) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have he : 2*(m+1)+2=(2*m+2)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

/-- Source-exact complementary two-class high-halting family exclusion. -/
theorem high_stop_two_lattices_alt (j m k time : Nat)
    (hm : 4≤m)
    (hclass : (j%8=1 ∧ (j+3*m)%32=15) ∨
              (j%8=5 ∧ (j+3*m)%32=31))
    (hstop : k+j+3*m+5=(2:Nat)^(2*m+2)*(j+3)) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (2*j+3,k) := by
  have hpow32 : 32 ∣ (2:Nat)^(2*m+2) := by
    have hd : (2:Nat)^5 ∣ 2^(2*m+2) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa using hd
  rcases hpow32 with ⟨q,hq⟩
  have hmod : (k+j+3*m+5)%32=0 := by
    apply Nat.mod_eq_zero_of_dvd
    refine ⟨q*(j+3),?_⟩
    calc
      k+j+3*m+5=(2:Nat)^(2*m+2)*(j+3) := hstop
      _=(32*q)*(j+3) := by rw [hq]
      _=32*(q*(j+3)) := by ac_rfl
  have hpow := power_linear_alt m
  have hp1 : 1≤(2:Nat)^(2*m+2) := Nat.pow_pos (by decide)
  have hjbound : j≤(2:Nat)^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp1
  have hmargin : 3*(4*m+4) ≤ 3*(2:Nat)^(2*m+2) :=
    Nat.mul_le_mul_left 3 hpow
  have hmult : (2:Nat)^(2*m+2)*(j+3)=
      (2:Nat)^(2*m+2)*j+3*(2:Nat)^(2*m+2) := by
    rw [Nat.mul_add]
    ac_rfl
  have hsize : 36≤k := by
    rw [hmult] at hstop
    omega
  rcases hclass with ⟨hj,hsum⟩ | ⟨hj,hsum⟩
  · have hk : k%32=12 := by omega
    let s := (j-1)/8
    let t := (k-12)/32
    have hs : j=8*s+1 := by dsimp [s]; omega
    have ht : k=32*t+12 := by dsimp [t]; omega
    have hx : 2*j+3=16*s+5 := by omega
    rw [hx,ht]
    exact blank_no_sector_c time s t
  · have hk : k%32=28 := by omega
    let s := (j-5)/8
    let t := (k-28)/32
    have hs : j=8*s+5 := by dsimp [s]; omega
    have ht : k=32*t+28 := by dsimp [t]; omega
    have hx : 2*j+3=16*s+13 := by omega
    rw [hx,ht]
    exact blank_no_sector_d time s t

/-- Four disjoint infinite high stopping parameter classes are impossible
    on the genuine Machine C blank section orbit. -/
theorem high_stop_four_lattices (j m k time : Nat)
    (hm : 4≤m)
    (hclass :
      (j%8=3 ∧ (j+3*m)%32=23) ∨
      (j%8=7 ∧ (j+3*m)%32=7) ∨
      (j%8=1 ∧ (j+3*m)%32=15) ∨
      (j%8=5 ∧ (j+3*m)%32=31))
    (hstop : k+j+3*m+5=(2:Nat)^(2*m+2)*(j+3)) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (2*j+3,k) := by
  rcases hclass with h1 | h2 | h3 | h4
  · exact high_stop_two_lattices j m k time hm (Or.inl h1) hstop
  · exact high_stop_two_lattices j m k time hm (Or.inr h2) hstop
  · exact high_stop_two_lattices_alt j m k time hm (Or.inl h3) hstop
  · exact high_stop_two_lattices_alt j m k time hm (Or.inr h4) hstop

#print axioms high_stop_two_lattices_alt
#print axioms high_stop_four_lattices
end BB6.Agent4Three
