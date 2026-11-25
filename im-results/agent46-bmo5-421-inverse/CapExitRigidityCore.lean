import Std
import Lean.Elab.Tactic.Omega
namespace CapExitRigidity
theorem residue_rigid {D u v x y : Nat} (hu : D ∣ u) (hv : D ∣ v)
    (hx : x<D) (hy : y<D) (he : u+x=v+y) : x=y := by
  have h := congrArg (fun n : Nat => n%D) he
  rw [Nat.add_mod,Nat.add_mod (a:=v),Nat.mod_eq_zero_of_dvd hu,Nat.mod_eq_zero_of_dvd hv] at h
  simpa [Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hy] using h

theorem pow_dvd_of_le {a b : Nat} (h : a≤b) : 3^a ∣ 3^b := by
  refine ⟨3^(b-a),?_⟩
  rw [←Nat.pow_add,show a+(b-a)=b by omega]

theorem exit_rigid {P d q q' p p' a b : Nat}
    (h1 : 3^a*q+3=2*P+p)
    (h2 : 3^b*q'+3=2*(2^d*P)+p')
    (hgap : 2^d*p+3<3^(min a b))
    (hgap' : p'+3*2^d<3^(min a b)) :
    p'+3*2^d=2^d*p+3 := by
  have hu : 3^(min a b) ∣ 3^b*q' := Nat.dvd_mul_right_of_dvd (pow_dvd_of_le (Nat.min_le_right ..)) _
  have hv : 3^(min a b) ∣ 2^d*(3^a*q) := by
    exact Nat.dvd_mul_left_of_dvd (Nat.dvd_mul_right_of_dvd (pow_dvd_of_le (Nat.min_le_left ..)) _) _
  have h := congrArg (fun n : Nat => 2^d*n) h1
  simp only [Nat.mul_add] at h
  have he : 3^b*q'+(2^d*p+3)=2^d*(3^a*q)+(p'+3*2^d) := by
    rw [show 2^d*(2*P)=2*(2^d*P) by ac_rfl,show 2^d*3=3*2^d by ac_rfl] at h
    omega
  exact (residue_rigid hu hv hgap hgap' he).symm

theorem regular_fail_exponent {k q p r a b : Nat}
    (h1 : 3^a*q+3=10*2^k+p)
    (h2 : 3^b*p+3=20*2^k+r)
    (hp : k+7≤p) (hr : r≤k+7) :
    3^a≤2*p+3 ∨ 3^b≤2*p+3 := by
  by_cases ha : 3^a≤2*p+3
  · exact Or.inl ha
  · by_cases hb : 3^b≤2*p+3
    · exact Or.inr hb
    · have hm : 2*p+3<3^(min a b) := by
        rw [Nat.min_def]
        split <;> omega
      have h1' : 3^a*q+3=2*(5*2^k)+p := by omega
      have h2' : 3^b*p+3=2*(2^1*(5*2^k))+r := by omega
      have h := exit_rigid (d:=1) h1' h2' (by omega) (by omega : r+3*2^1<3^(min a b))
      simp at h
      omega

theorem regular_fail_product {k q p r a b : Nat}
    (h1 : 3^a*q+3=10*2^k+p)
    (h2 : 3^b*p+3=20*2^k+r)
    (hp : k+7≤p) (hr : r≤k+7) (hrlo : 2≤r) :
    2*2^k≤q*p ∨ 4*2^k≤p*p := by
  rcases regular_fail_exponent h1 h2 hp hr with ha|hb
  · left
    have hA : 3^a≤5*p := by omega
    have h := Nat.mul_le_mul_right q hA
    rw [show 5*p*q=5*(q*p) by ac_rfl] at h
    omega
  · right
    have hB : 3^b≤5*p := by omega
    have h := Nat.mul_le_mul_right p hB
    rw [show 5*p*p=5*(p*p) by ac_rfl] at h
    omega

#print axioms exit_rigid
#print axioms regular_fail_exponent
#print axioms regular_fail_product
end CapExitRigidity
