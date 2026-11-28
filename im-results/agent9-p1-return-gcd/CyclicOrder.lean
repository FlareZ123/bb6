import AntiGenericScaled
import OrderReturn
set_option maxHeartbeats 0

namespace BB6.Agent9CyclicOrder
open BB6.Agent9ReturnGCD BB6.Agent9AntiGenericBound BB6.Agent9AntiGenericScaled BB6.Agent43OrderReturn

/-- A positive interior slope of odd modulus h, with a known doubling
    order K coprime to h, cannot accompany a bounded affine-clock carry
    for K+B steps when h*(C+K+1)<2^B.

    In contrast to the general order-return argument, only one K-shifted
    copy of the coordinate is needed. The mixed determinant
      E_j = h*(c_(j+K)-c_j) - dir*K*a_j
    halves at every step; coprimality then excludes its zero value. -/
theorem no_coprime_cyclic
    (h K B L : Nat) (q dir C : Int) (a c x : Nat → Int)
    (hh : 0<h) (hodd : (h:Int)%2=1)
    (hco : Nat.Coprime h K)
    (horder : (h:Int) ∣ (2:Int)^K-1) (hK : 0<K)
    (hdir : dir=1 ∨ dir= -1) (hL : K+B≤L)
    (hinner : ∀ j≤L, 0<a j ∧ a j<(h:Int))
    (hx : ∀ j<L, x j=0 ∨ x j=1)
    (ha : ∀ j<L, 2*a (j+1)=a j+(h:Int)*x j)
    (hc : ∀ j<L, 2*c (j+1)=c j+(q+dir*(j:Int))*x j)
    (hbound : ∀ j≤L, 1≤c j ∧ c j≤C)
    (hscale : (h:Int)*(C+(K:Int)+1)<(2:Int)^B) : False := by
  have hret : a K=a 0 :=
    order_return (h:Int) a x K horder (hinner 0 (by omega))
      (hinner K (by omega)) (fun j hj => ha j (by omega))
  have hperiod := slope_return_period (h:Int) a x L K hodd
    (by omega) hret hx ha
  let E : Nat → Int := fun j =>
    (h:Int)*(c (j+K)-c j)-dir*(K:Int)*a j
  have hhalf : ∀ j<B, 2*E (j+1)=E j := by
    intro j hj
    have h0 := hc j (by omega)
    have h1 := hc (j+K) (by omega)
    have hper := hperiod j (by omega)
    have hclock : q+dir*((j+K:Nat):Int)=
        (q+dir*(j:Int))+dir*(K:Int) := by
      simp only [Int.natCast_add,Int.mul_add]
      omega
    rw [hclock,hper] at h1
    have hdiff : 2*(c (j+K+1)-c (j+1)) =
        (c (j+K)-c j)+dir*(K:Int)*x j := by
      simp only [Int.add_mul] at h0 h1
      omega
    have hA := ha j (by omega)
    dsimp [E]
    rw [show j+1+K=j+K+1 by omega]
    calc
      2*((h:Int)*(c (j+K+1)-c (j+1))-dir*(K:Int)*a (j+1)) =
          (h:Int)*(2*(c (j+K+1)-c (j+1))) -
            dir*(K:Int)*(2*a (j+1)) := by
            simp only [Int.mul_sub,Int.mul_assoc]
            ac_rfl
      _ = (h:Int)*((c (j+K)-c j)+dir*(K:Int)*x j) -
            dir*(K:Int)*(a j+(h:Int)*x j) := by rw [hdiff,hA]
      _ = (h:Int)*(c (j+K)-c j)-dir*(K:Int)*a j := by
        simp only [Int.mul_add,Int.mul_sub]
        have heq : (h:Int)*(dir*(K:Int)*x j) =
            dir*(K:Int)*((h:Int)*x j) := by ac_rfl
        rw [heq]
        omega
  have hEbound : -(2:Int)^B<E 0 ∧ E 0<(2:Int)^B := by
    have hi := interior_energy_bound (h:Int) C ((h:Int)-a 0)
      (c K) (c 0) dir K B (by omega)
      ⟨(hbound K (by omega)).1,(hbound K (by omega)).2,
        (hbound 0 (by omega)).1,(hbound 0 (by omega)).2⟩
      (by have hh0 := hinner 0 (by omega); omega)
      hdir hscale
    simpa only [E,Nat.zero_add,Int.sub_sub,Int.mul_sub,
      Int.mul_add] using hi
  have hEzero := finite_half_zero E B hhalf hEbound
  have hdiv : (h:Int) ∣ dir*(K:Int)*a 0 := by
    refine ⟨c K-c 0,?_⟩
    dsimp [E] at hEzero
    simp only [Nat.zero_add] at hEzero
    omega
  have hdivK : (h:Int) ∣ (K:Int)*a 0 := by
    rcases hdir with hd|hd
    · simpa [hd] using hdiv
    · have hneg : (h:Int) ∣ -(dir*(K:Int)*a 0) :=
        Int.dvd_neg.mpr hdiv
      simpa [hd] using hneg
  have hnat : h ∣ K*(a 0).natAbs := by
    have hh' := Int.natAbs_dvd_natAbs.mpr hdivK
    simpa only [Int.natAbs_mul,Int.natAbs_natCast] using hh'
  have hA : h ∣ (a 0).natAbs := hco.dvd_of_dvd_mul_left hnat
  have hI : (h:Int) ∣ a 0 :=
    Int.natAbs_dvd_natAbs.mp (by simpa using hA)
  have hz : a 0%(h:Int)=0 := Int.emod_eq_zero_of_dvd hI
  have hi : a 0%(h:Int)=a 0 :=
    Int.emod_eq_of_lt (by omega) (hinner 0 (by omega)).2
  omega

/-- Shortened positive-clock obstruction under a supplied Mersenne order.
    Compared with the 2*K+B interior window in OrderReturn, this uses K+B.
    The extra r positions remove the dyadic part of the original slope. -/
theorem no_scaled_cyclic
    (h K A r B L : Nat) (q dir C g : Int)
    (a c w x : Nat → Int)
    (hh : 0<h) (hodd : (h:Int)%2=1)
    (hco : Nat.Coprime h K) (horder : (h:Int)∣(2:Int)^K-1)
    (hK : 0<K)
    (hdir : dir=1 ∨ dir= -1)
    (hg : g=(2:Int)^r*(h:Int))
    (hL : A+r+K+B≤L)
    (hinit : -(2:Int)^(A+r)<a 0 ∧
      a 0<g+(2:Int)^(A+r))
    (hx : ∀ j<L, x j=0 ∨ x j=1)
    (ha : ∀ j<L, 2*a (j+1)=a j+g*x j)
    (hc : ∀ j<L, 2*c (j+1)=c j+(q+dir*(j:Int))*x j)
    (hw : ∀ j<L, 2*w (j+1)=w j+(q+dir*(j:Int))*(1-x j))
    (hbound : ∀ j≤L, 1≤c j ∧ c j≤C ∧ 1≤w j ∧ w j≤C)
    (hscale : (h:Int)*(C+(K:Int)+1)<(2:Int)^B) : False := by
  obtain ⟨b,_,hb,hinit'⟩ :=
    scale_slope g h L r A a x hg ha (by omega) hinit
  have hconf := slope_confined (h:Int) b x A (by omega)
    (fun j hj => hx j (by omega))
    (fun j hj => hb j (by omega)) hinit'
  have hCpos : 0≤C+(K:Int)+1 := by
    have hh0 := hbound 0 (by omega)
    omega
  have hmult := Int.mul_le_mul_of_nonneg_right
    (show 1≤(h:Int) by omega) hCpos
  have hcB : C<(2:Int)^B := by omega
  by_cases h0 : b A=0
  · have hlock := odd_boundary_lock (h:Int) b x A B hodd
      (Or.inl h0) (fun j hj => hx j (by omega))
      (fun j hj => hb j (by omega))
    apply no_positive_halves (fun j => c (A+j)) B
    · intro j hj
      have h := hc (A+j) (by omega)
      have he := hlock j hj
      simp [h0] at he
      rw [he] at h
      simpa only [Nat.add_assoc,Int.mul_zero,Int.add_zero] using h
    · exact (hbound (A+B) (by omega)).1
    · exact Int.lt_of_le_of_lt (hbound A (by omega)).2.1 hcB
  by_cases hmax : b A=(h:Int)
  · have hlock := odd_boundary_lock (h:Int) b x A B hodd
      (Or.inr hmax) (fun j hj => hx j (by omega))
      (fun j hj => hb j (by omega))
    apply no_positive_halves (fun j => w (A+j)) B
    · intro j hj
      have h := hw (A+j) (by omega)
      have he := hlock j hj
      simp [h0] at he
      rw [he] at h
      simpa only [Nat.add_assoc,Int.sub_self,Int.mul_zero,Int.add_zero] using h
    · exact (hbound (A+B) (by omega)).2.2.1
    · exact Int.lt_of_le_of_lt (hbound A (by omega)).2.2.2 hcB
  have hstart : 0<b A ∧ b A<(h:Int) := by omega
  have hinner : ∀ j≤L-r-A, 0<b (A+j) ∧ b (A+j)<(h:Int) := by
    intro j hj
    induction j with
    | zero => simpa using hstart
    | succ j ih =>
      have hh0 := ih (by omega)
      have hstep := hb (A+j) (by omega)
      have hbit := hx (A+j) (by omega)
      rw [show A+(j+1)=A+j+1 by omega]
      rcases hbit with hbit|hbit <;> rw [hbit] at hstep <;> omega
  apply no_coprime_cyclic h K B (L-r-A) (q+dir*(A:Int)) dir C
    (fun j => b (A+j)) (fun j => c (A+j))
    (fun j => x (A+j))
    hh hodd hco horder hK hdir (by omega) hinner
  · intro j hj; exact hx (A+j) (by omega)
  · intro j hj; simpa only [Nat.add_assoc] using hb (A+j) (by omega)
  · intro j hj
    have h := hc (A+j) (by omega)
    simpa only [Nat.add_assoc,Int.natCast_add,Int.mul_add,
      Int.add_assoc,Int.add_left_comm,Int.add_comm] using h
  · intro j hj
    have hbnd := hbound (A+j) (by omega)
    exact ⟨hbnd.1,hbnd.2.1⟩
  · exact hscale

#print axioms no_coprime_cyclic
#print axioms no_scaled_cyclic
end BB6.Agent9CyclicOrder
