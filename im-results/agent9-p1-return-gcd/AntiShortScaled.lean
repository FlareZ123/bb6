import AntiShort
import AntiGenericScaled
set_option maxHeartbeats 0
namespace BB6.Agent9AntiShortScaled
open BB6.Agent9ReturnGCD BB6.Agent9AntiGenericScaled BB6.Agent9AntiShort

/-- Any 2^r multiple of an odd h dividing 2^K+1, without any coprimality condition,
    forbids a K-shift antiperiodic factor once the positive coordinates
    outlive their logarithmic capacity. -/
theorem no_scaled_antishort (h K A r B L : Nat) (q dir C g : Int)
    (a c w x : Nat→Int)
    (hh : 0<h) (hodd : (h:Int)%2=1)
    (hmod : (h:Int)∣(2:Int)^K+1) (hK : 0<K)
    (hdir : dir=1∨dir= -1)
    (hg : g=(2:Int)^r*(h:Int)) (hL : A+r+K+B≤L)
    (hinit : -(2:Int)^(A+r)<a 0 ∧ a 0<g+(2:Int)^(A+r))
    (hx : ∀ j<L, x j=0∨x j=1)
    (ha : ∀ j<L, 2*a (j+1)=a j+g*x j)
    (hc : ∀ j<L, 2*c (j+1)=c j+(q+dir*(j:Int))*x j)
    (hw : ∀ j<L, 2*w (j+1)=w j+(q+dir*(j:Int))*(1-x j))
    (hbound : ∀ j≤L, 1≤c j ∧ c j≤C ∧ 1≤w j ∧ w j≤C)
    (hscale : (h:Int)*(C+(K:Int)+1)<(2:Int)^B) : False := by
  obtain ⟨b,_,hb,hinit'⟩ := scale_slope g h L r A a x hg ha (by omega) hinit
  have hconf := slope_confined (h:Int) b x A (by omega)
    (fun j hj => hx j (by omega))
    (fun j hj => hb j (by omega)) hinit'
  have hCpos : 0≤C+(K:Int)+1 := by
    have hh0 := hbound 0 (by omega)
    omega
  have hmult := Int.mul_le_mul_of_nonneg_right (show 1≤(h:Int) by omega) hCpos
  have hcB : C<(2:Int)^B := by omega
  by_cases h0 : b A=0
  · have hlock := odd_boundary_lock (h:Int) b x A B hodd (Or.inl h0)
      (fun j hj => hx j (by omega)) (fun j hj => hb j (by omega))
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
  · have hlock := odd_boundary_lock (h:Int) b x A B hodd (Or.inr hmax)
      (fun j hj => hx j (by omega)) (fun j hj => hb j (by omega))
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
  apply no_short_negacyclic (q+dir*(A:Int)) dir C (h:Int) K B (L-r-A)
    (fun j => b (A+j)) (fun j => c (A+j)) (fun j => w (A+j)) (fun j => x (A+j))
    hodd hmod hK hdir (by omega) hinner
  · intro j hj; exact hx (A+j) (by omega)
  · intro j hj; simpa only [Nat.add_assoc] using hb (A+j) (by omega)
  · intro j hj
    have h := hc (A+j) (by omega)
    simpa only [Nat.add_assoc,Int.natCast_add,Int.mul_add,
      Int.add_assoc,Int.add_left_comm,Int.add_comm] using h
  · intro j hj
    have h := hw (A+j) (by omega)
    simpa only [Nat.add_assoc,Int.natCast_add,Int.mul_add,
      Int.add_assoc,Int.add_left_comm,Int.add_comm] using h
  · intro j hj
    exact hbound (A+j) (by omega)
  · exact hscale

#print axioms no_scaled_antishort
end BB6.Agent9AntiShortScaled
