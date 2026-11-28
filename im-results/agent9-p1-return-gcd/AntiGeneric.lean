import AntiShiftCore
import AntiNegacyclic
set_option maxHeartbeats 0
namespace BB6.Agent9AntiGeneric
open BB6.Agent9AntiShift BB6.Agent9AntiNegacyclic

/-- Every odd-modulus antiperiodic carry with coprime offset and confined
    positive coordinates contradicts sufficiently strong initial decay. -/
theorem no_coprime_antishift (h K B L : Nat) (q dir : Int)
    (a c w x : Nat→Int)
    (hh : 0<h) (hco : Nat.Coprime h K)
    (hdir : dir=1∨dir= -1) (hL : K+B≤L)
    (hinner : ∀ j≤B, 0<a j ∧ a j<(h:Int))
    (hx : ∀ j<B, x j=0∨x j=1)
    (hflip : ∀ j<B, x (j+K)=1-x j)
    (ha : ∀ j<B, 2*a (j+1)=a j+(h:Int)*x j)
    (hc : ∀ j<L, 2*c (j+1)=c j+(q+dir*(j:Int))*x j)
    (hw : ∀ j<B, 2*w (j+1)=w j+(q+dir*(j:Int))*(1-x j))
    (hE0 : -(2:Int)^B < (h:Int)*(c K-w 0)+dir*(K:Int)*a 0-dir*(K:Int)*(h:Int) ∧
          (h:Int)*(c K-w 0)+dir*(K:Int)*a 0-dir*(K:Int)*(h:Int) < (2:Int)^B) : False := by
  have hdiv := antishift_divisibility (h:Int) q dir K B L a c w x hdir hL hx hflip
    ha hc hw hE0
  have hd : (h:Int) ∣ (K:Int)*(a B-(h:Int)) := by
    rcases hdir with he|he
    · simpa [he] using hdiv
    · have hneg : (h:Int) ∣ -(dir*(K:Int)*(a B-(h:Int))) := by
        exact Int.dvd_neg.mpr hdiv
      have hsgn : -(dir*(K:Int)*(a B-(h:Int)))=(K:Int)*(a B-(h:Int)) := by
        rw [he,Int.mul_assoc,Int.neg_one_mul]
        simp
      rw [hsgn] at hneg
      exact hneg
  have hdN : h ∣ K*(a B-(h:Int)).natAbs := by
    have habs := Int.natAbs_dvd_natAbs.mpr hd
    simpa only [Int.natAbs_mul,Int.natAbs_natCast] using habs
  have hrest : h ∣ (a B-(h:Int)).natAbs := hco.dvd_of_dvd_mul_left hdN
  have hrestI : (h:Int)∣a B-(h:Int) := by
    exact Int.natAbs_dvd_natAbs.mp (by simpa using hrest)
  obtain ⟨z,hz⟩ := hrestI
  have hdA : (h:Int)∣a B := by
    refine ⟨z+1,?_⟩
    rw [Int.mul_add,Int.mul_one]
    omega
  have h0 : a B%(h:Int)=0 := Int.emod_eq_zero_of_dvd hdA
  have hBi := hinner B (by omega)
  have h1 : a B%(h:Int)=a B :=
    Int.emod_eq_of_lt (by omega) hBi.2
  omega

/-- General negacyclic carry obstruction: if the odd slope modulus h
    divides 2^K+1 and is coprime to K, the selected word must violate an
    anti-shift somewhere in every sufficiently long positive path. -/
theorem no_coprime_negacyclic (h K B L : Nat) (q dir : Int)
    (a c w x : Nat→Int)
    (hh : 0<h) (hco : Nat.Coprime h K)
    (hmod : (h:Int) ∣ (2:Int)^K+1)
    (hdir : dir=1∨dir= -1) (hL : K+B≤L)
    (hinner : ∀ j≤L, 0<a j ∧ a j<(h:Int))
    (hx : ∀ j<L, x j=0∨x j=1)
    (ha : ∀ j<L, 2*a (j+1)=a j+(h:Int)*x j)
    (hc : ∀ j<L, 2*c (j+1)=c j+(q+dir*(j:Int))*x j)
    (hw : ∀ j<L, 2*w (j+1)=w j+(q+dir*(j:Int))*(1-x j))
    (hE0 : -(2:Int)^B < (h:Int)*(c K-w 0)+dir*(K:Int)*a 0-dir*(K:Int)*(h:Int) ∧
          (h:Int)*(c K-w 0)+dir*(K:Int)*a 0-dir*(K:Int)*(h:Int) < (2:Int)^B) : False := by
  apply no_coprime_antishift h K B L q dir a c w x hh hco hdir hL
    (fun j hj => hinner j (by omega))
    (fun j hj => hx j (by omega))
    (fun j hj => bits_negacyclic (h:Int) K L a x (by omega) hmod hinner hx ha j (by omega))
    (fun j hj => ha j (by omega))
    (fun j hj => hc j (by omega))
    (fun j hj => hw j (by omega)) hE0

#print axioms no_coprime_antishift
#print axioms no_coprime_negacyclic
end BB6.Agent9AntiGeneric
