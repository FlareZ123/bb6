import Std
import Lean.Elab.Tactic.Omega
namespace CapExitWord
def exponent (a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | t+1 => exponent a t + a t

def coeff (a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | t+1 => 3^(a t)*coeff a t+2^t

def offset (a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | t+1 => 3^(a t)*offset a t+1

theorem expansion (k : Nat) (a q : Nat → Nat) (t : Nat)
    (he : ∀ j, j<t → q (j+1)+10*2^(k+j)=3^(a j)*q j+3) :
    3^(exponent a t)*q 0+3*offset a t=q t+10*2^k*coeff a t := by
  induction t with
  | zero => simp [exponent,offset,coeff]
  | succ t ih =>
    have h := ih (fun j hj => he j (by omega))
    have h1 := congrArg (fun x : Nat => 3^(a t)*x) h
    have h2 := he t (by omega)
    simp only [Nat.mul_add] at h1
    rw [exponent,offset,coeff,Nat.pow_add,Nat.mul_add,Nat.mul_add]
    rw [Nat.pow_add] at h2
    rw [show 3^(exponent a t)*3^(a t)*q 0=3^(a t)*(3^(exponent a t)*q 0) by ac_rfl,
        show 3*(3^(a t)*offset a t)=3^(a t)*(3*offset a t) by ac_rfl,
        show 10*2^k*(3^(a t)*coeff a t)=3^(a t)*(10*2^k*coeff a t) by ac_rfl]
    rw [show 10*2^k*2^t=10*(2^k*2^t) by ac_rfl]
    omega

theorem offset_le_coeff (a : Nat → Nat) (t : Nat) : offset a t≤coeff a t := by
  induction t with
  | zero => simp [offset,coeff]
  | succ t ih =>
    have hm := Nat.mul_le_mul_left (3^(a t)) ih
    have hp : 0<2^t := Nat.pow_pos (by decide)
    simp only [offset,coeff]
    omega

theorem coeff_pos (a : Nat → Nat) {t : Nat} (ht : 0<t) : 0<coeff a t := by
  cases t with
  | zero => omega
  | succ t =>
    have hp : 0<2^t := Nat.pow_pos (by decide)
    rw [coeff]; omega

theorem pow3_mod (n : Nat) (h : 0<n) : 3^n%3=0 := by
  obtain ⟨m,rfl⟩ : ∃ m,n=m+1 := ⟨n-1,by omega⟩
  rw [Nat.pow_succ]; omega

theorem two_unit (n : Nat) : 2^n%3=1 ∨ 2^n%3=2 := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ,Nat.mul_mod]; rcases ih with h|h <;> rw [h] <;> decide

theorem coeff_mod (a : Nat → Nat) (t : Nat) (ha : 0<a t) : coeff a (t+1)%3=2^t%3 := by
  rw [coeff,Nat.add_mod,Nat.mul_mod,pow3_mod _ ha]
  simp

theorem exponent_pos (a : Nat → Nat) {t : Nat} (ht : 0<t) (ha : ∀ j,j<t → 0<a j) : 0<exponent a t := by
  cases t with
  | zero => omega
  | succ t => have := ha t (by omega); simp only [exponent]; omega

theorem nonzero (k : Nat) (a : Nat → Nat) (q t : Nat) (ht : 0<t)
    (ha : ∀ j,j<t → 0<a j) : 3^(exponent a t)*q≠10*2^k*coeff a t := by
  have he := pow3_mod _ (exponent_pos a ht ha)
  obtain ⟨s,rfl⟩ : ∃ s,t=s+1 := ⟨t-1,by omega⟩
  have hc := coeff_mod a s (ha s (by omega))
  intro h
  have hm := congrArg (fun x : Nat => x%3) h
  rw [Nat.mul_mod,he,Nat.zero_mul,Nat.zero_mod,Nat.mul_mod (a:=10*2^k),hc,Nat.mul_mod (a:=10)] at hm
  rcases two_unit k with hk|hk <;> rcases two_unit s with hs|hs <;> simp [hk,hs] at hm

theorem initial_exp_le (a : Nat → Nat) {t : Nat} (ht : 0<t) : a 0≤exponent a t := by
  induction t with
  | zero => omega
  | succ t ih =>
    cases t with
    | zero => simp [exponent]
    | succ t =>
      have hh := ih (by omega)
      change a 0≤exponent a (t+1)+a (t+1)
      omega

theorem coeff_bound (a : Nat → Nat) {t : Nat} (ht : 0<t) :
    coeff a t<2^t*3^(exponent a t-a 0) := by
  induction t with
  | zero => omega
  | succ t ih =>
    cases t with
    | zero => simp [coeff,exponent]
    | succ t =>
      have ht' : 0<t+1 := by omega
      have h := ih ht'
      have hA := initial_exp_le a ht'
      have hE : exponent a (t+1+1)-a 0=(exponent a (t+1)-a 0)+a (t+1) := by
        change exponent a (t+1)+a (t+1)-a 0=(exponent a (t+1)-a 0)+a (t+1)
        omega
      rw [coeff,hE,Nat.pow_add 3 (exponent a (t+1)-a 0) (a (t+1)),Nat.pow_succ 2 (t+1)]
      have hp : 0<3^(a (t+1)) := Nat.pow_pos (by decide)
      have hh := Nat.mul_lt_mul_of_pos_left h hp
      rw [show 3^(a (t+1))*(2^(t+1)*3^(exponent a (t+1)-a 0))=2^(t+1)*(3^(exponent a (t+1)-a 0)*3^(a (t+1))) by ac_rfl] at hh
      have hpos : 1≤3^(exponent a (t+1)-a 0)*3^(a (t+1)) := Nat.mul_pos (Nat.pow_pos (by decide)) hp
      have hM := Nat.mul_le_mul_left (2^(t+1)) hpos
      rw [Nat.mul_one] at hM
      rw [show 2^(t+1)*2*(3^(exponent a (t+1)-a 0)*3^(a (t+1)))=2*(2^(t+1)*(3^(exponent a (t+1)-a 0)*3^(a (t+1)))) by ac_rfl]
      omega

#print axioms expansion
#print axioms nonzero
#print axioms coeff_bound
end CapExitWord
