import CThreeSource
import Lean.Elab.Tactic.Omega

namespace BB6.Agent4Three
open BB6.Agent46

private theorem power_linear (m : Nat) :
    4*m+4 ≤ (2:Nat)^(2*m+2) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have he : 2*(m+1)+2=(2*m+2)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

/-- New infinite high-stopping lattice excluded from genuine Machine C root. -/
theorem high_stop_blank_unreachable (j m k time : Nat)
    (hm : 4≤m)
    (hj : j%8=3)
    (hclass : (j+3*m)%32=23)
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
  have hkm : k%32=4 := by omega
  have hpow := power_linear m
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
  let s := (j-3)/8
  have hs : j=8*s+3 := by dsimp [s]; omega
  let t := (k-36)/32
  have ht : k=32*t+36 := by dsimp [t]; omega
  have hx : 2*j+3=16*s+9 := by omega
  rw [hx,ht]
  exact blank_no_sector time s t

/-- A nonempty infinite family: j=3 and m=28 modulo 32. -/
theorem high_j3_m28_family (r time : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (9,(2:Nat)^(2*(28+32*r)+2)*6 - (3+3*(28+32*r)+5)) := by
  let m := 28+32*r
  let k := (2:Nat)^(2*m+2)*6 - (3+3*m+5)
  have hpow := power_linear m
  have hp : 1≤(2:Nat)^(2*m+2) := Nat.pow_pos (by decide)
  have hprod : 3+3*m+5 ≤ (2:Nat)^(2*m+2)*6 := by
    have h6 := Nat.mul_le_mul_left 6 hpow
    omega
  have hg : k+3+3*m+5=(2:Nat)^(2*m+2)*6 := by
    dsimp [k]
    omega
  have hr := high_stop_blank_unreachable 3 m k time
    (by dsimp [m]; omega) (by decide)
    (by dsimp [m]; omega) (by simpa using hg)
  simpa [k,m] using hr

#print axioms high_stop_blank_unreachable
#print axioms high_j3_m28_family
end BB6.Agent4Three
