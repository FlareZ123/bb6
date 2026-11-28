import AntiShortCore
import CyclicShort
import AntiGenericScaled
set_option maxHeartbeats 0

namespace BB6.Agent9AntiShort
open BB6.Agent9ReturnGCD BB6.Agent9AntiShortCore BB6.Agent9AntiShift
open BB6.Agent9AntiNegacyclic BB6.Agent9AntiGenericBound BB6.Agent9CyclicShort

/-- Coprimality-free K+B-window negacyclic obstruction.

    If h divides 2^K+1 and an interior odd slope survives K+B steps,
    the anti-shift determinant forces h|K*a(B), hence h|K*a(0) by
    *backward* divisibility. Negacyclicity gives a(K)=h-a(0), and
    h|K*a(K). Backward propagation across K yields K distinct
    integral quotient candidates in the (K-1)-point interval (0,K).
    A quotient collision produces an actual return p<K, contradicted
    by the shortened cyclic return obstruction over the same K+B
    window. Thus gcd(h,K)=1 is unnecessary. -/
theorem no_short_negacyclic
    (q dir C h : Int) (K B L : Nat)
    (a c w x : Nat → Int)
    (hodd : h%2=1) (hmod : h∣(2:Int)^K+1) (hK : 0<K)
    (hdir : dir=1∨dir= -1) (hL : K+B≤L)
    (hinside : ∀ j≤L, 0<a j ∧ a j<h)
    (hx : ∀ j<L, x j=0∨x j=1)
    (ha : ∀ j<L, 2*a (j+1)=a j+h*x j)
    (hc : ∀ j<L, 2*c (j+1)=c j+(q+dir*(j:Int))*x j)
    (hw : ∀ j<L, 2*w (j+1)=w j+(q+dir*(j:Int))*(1-x j))
    (hbound : ∀ j≤L, 1≤c j ∧ c j≤C ∧ 1≤w j ∧ w j≤C)
    (hscale : h*(C+(K:Int)+1)<(2:Int)^B) : False := by
  have hh : 0<h := by have hi := hinside 0 (by omega); omega
  have hE0 :
      -(2:Int)^B < h*(c K-w 0)+dir*(K:Int)*a 0-dir*(K:Int)*h ∧
        h*(c K-w 0)+dir*(K:Int)*a 0-dir*(K:Int)*h <
          (2:Int)^B := by
    exact interior_energy_bound h C (a 0) (c K) (w 0) dir K B
      hh ⟨(hbound K (by omega)).1,(hbound K (by omega)).2.1,
          (hbound 0 (by omega)).2.2.1,
          (hbound 0 (by omega)).2.2.2⟩
      (hinside 0 (by omega)) hdir hscale
  have hdiv := antishift_divisibility h q dir K B L a c w x
    hdir hL
    (fun j hj => hx j (by omega))
    (fun j hj => bits_negacyclic h K L a x hh hmod hinside hx ha j (by omega))
    (fun j hj => ha j (by omega))
    (fun j hj => hc j (by omega))
    (fun j hj => hw j (by omega)) hE0
  have hdB : h ∣ (K:Int)*(a B-h) := by
    rcases hdir with he|he
    · simpa [he] using hdiv
    · have hneg : h∣-(dir*(K:Int)*(a B-h)) :=
        Int.dvd_neg.mpr hdiv
      have hsgn : -(dir*(K:Int)*(a B-h))=(K:Int)*(a B-h) := by
        rw [he,Int.mul_assoc,Int.neg_one_mul]
        simp
      rw [hsgn] at hneg
      exact hneg
  have hdEnd : h ∣ (K:Int)*a B := by
    obtain ⟨z,hz⟩ := hdB
    refine ⟨z+(K:Int),?_⟩
    rw [Int.mul_sub] at hz
    rw [Int.mul_add]
    have hcomm : (K:Int)*h=h*(K:Int) := by ac_rfl
    rw [hcomm] at hz
    omega
  have hdAllB := backward_divisible h (K:Int) B a x
    (fun j hj => ha j (by omega)) hdEnd
  have hd0 : h∣(K:Int)*a 0 := hdAllB 0 (by omega)
  have hAK : a K=h-a 0 := by
    simpa only [Nat.zero_add] using
      (slope_negacyclic h K L a x hh hmod hinside ha 0 (by omega))
  have hdK : h ∣ (K:Int)*a K := by
    obtain ⟨z,hz⟩ := hd0
    refine ⟨(K:Int)-z,?_⟩
    rw [hAK,Int.mul_sub,Int.mul_sub]
    have hcomm : (K:Int)*h=h*(K:Int) := by ac_rfl
    rw [hcomm,hz]
    omega
  have hdAllK := backward_divisible h (K:Int) K a x
    (fun j hj => ha j (by omega)) hdK
  obtain ⟨p,hp,hpK,hret⟩ := divisible_cycle_has_short_return
    h K L a x hh hK (by omega) hinside hx ha hdAllK
  apply no_short_return_carry q dir C h K B L a c x
    hdir hodd _ hL hinside hx ha hc
    (fun j hj =>
      ⟨(hbound j hj).1,(hbound j hj).2.1⟩)
    hscale
  intro _
  exact ⟨p,hp,by omega,hret⟩

#print axioms no_short_negacyclic
end BB6.Agent9AntiShort
