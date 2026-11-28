import AntiGeneral
import AntiShiftCore
set_option maxHeartbeats 0
namespace BB6.Agent9AntiNegacyclic
open BB6.Agent9AntiGeneral

/-- A strictly positive submodular integer multiple of h is exactly h. -/
theorem positive_multiple_is_modulus (h a b : Int)
    (hh : 0<h) (ha : 0<a ∧ a<h) (hb : 0<b ∧ b<h)
    (hd : h∣a+b) : a+b=h := by
  obtain ⟨z,hz⟩ := hd
  have hp : 1≤z := by
    by_cases H : 1≤z
    · exact H
    · have hm := Int.mul_le_mul_of_nonneg_left (show z≤0 by omega) (by omega : 0≤h)
      omega
  have hq : z≤1 := by
    by_cases H : z≤1
    · exact H
    · have hm := Int.mul_le_mul_of_nonneg_left (show 2≤z by omega) (by omega : 0≤h)
      omega
  have hone : z=1 := by omega
  rw [hone] at hz
  simpa using hz

/-- Integer doubling carries in the interior of a modulus dividing 2^K+1
    have an exact K-antiperiodic slope, without a finite-state enumeration. -/
theorem slope_negacyclic (h : Int) (K L : Nat)
    (a x : Nat→Int)
    (hh : 0<h)
    (hdiv : h∣(2:Int)^K+1)
    (hinside : ∀ j≤L, 0<a j ∧ a j<h)
    (hs : ∀ j<L, 2*a (j+1)=a j+h*x j) :
    ∀ j, j+K≤L → a (j+K)=h-a j := by
  intro j hj
  have hblock := block_of_halves a (fun t=>h*x t) j K L hs hj
  rw [wordSum_scale x j K h] at hblock
  obtain ⟨z,hz⟩ := hdiv
  have hsum : h ∣ a (j+K)+a j := by
    refine ⟨z*a (j+K)-wordSum x j K,?_⟩
    calc
      a (j+K)+a j = ((2:Int)^K+1)*a (j+K) - ((2:Int)^K*a (j+K)-a j) := by
        rw [Int.add_mul]
        omega
      _ = (h*z)*a (j+K)-h*wordSum x j K := by
        rw [hz,hblock]; omega
      _ = h*(z*a (j+K)-wordSum x j K) := by rw [Int.mul_sub]; ac_rfl
  have hsum' := positive_multiple_is_modulus h (a (j+K)) (a j) hh
    (hinside (j+K) hj) (hinside j (by omega)) hsum
  omega

/-- The bit word itself is complemented at a K-shift. -/
theorem bits_negacyclic (h : Int) (K L : Nat)
    (a x : Nat→Int)
    (hh : 0<h)
    (hdiv : h∣(2:Int)^K+1)
    (hinside : ∀ j≤L, 0<a j ∧ a j<h)
    (hx : ∀ j<L, x j=0∨x j=1)
    (hs : ∀ j<L, 2*a (j+1)=a j+h*x j) :
    ∀ j, j+K+1≤L → x (j+K)=1-x j := by
  intro j hj
  have h0 := slope_negacyclic h K L a x hh hdiv hinside hs j (by omega)
  have h1 := slope_negacyclic h K L a x hh hdiv hinside hs (j+1) (by omega)
  have hs0 := hs j (by omega)
  have hsK := hs (j+K) (by omega)
  rw [show (j+1)+K=j+K+1 by omega] at h1
  have hx0 := hx j (by omega)
  have hxK := hx (j+K) (by omega)
  rcases hx0 with hx0|hx0 <;> rcases hxK with hxK|hxK <;>
    rw [hx0] at hs0 ⊢ <;> rw [hxK] at hsK ⊢ <;>
    simp at hs0 hsK ⊢ <;> omega

#print axioms positive_multiple_is_modulus
#print axioms slope_negacyclic
#print axioms bits_negacyclic
end BB6.Agent9AntiNegacyclic
