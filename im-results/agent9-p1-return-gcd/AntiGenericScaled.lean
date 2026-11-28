import AntiGeneric
import AntiGenericBound
import ReturnScaled
set_option maxHeartbeats 0
namespace BB6.Agent9AntiGenericScaled
open BB6.Agent9AntiGeneric BB6.Agent9AntiGenericBound BB6.Agent9ReturnGCD

/-- A nontrivial odd slope cannot escape either boundary without an
    impossible half-integral transition. -/
theorem odd_boundary_lock (g : Int) (a x : Nat→Int) (A K : Nat)
    (hodd : g%2=1) (hz : a A=0∨a A=g)
    (hx : ∀ j<A+K, x j=0∨x j=1)
    (hs : ∀ j<A+K, 2*a (j+1)=a j+g*x j) :
    ∀ j<K, x (A+j)=if a A=0 then 0 else 1 := by
  have hg0 : g≠0 := by
    intro he
    rw [he] at hodd
    simp at hodd
  have hodd' : ∀ z:Int, 2*z≠g := by
    intro z heq
    have hd : (2:Int)∣g := ⟨z,by omega⟩
    have hr := Int.emod_eq_zero_of_dvd hd
    omega
  have h : ∀ j≤K, a (A+j)=a A := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
      have hp := ih (by omega)
      have hr := hs (A+j) (by omega)
      have hb := hx (A+j) (by omega)
      have hp' : 2*a (A+j+1)=a (A+j)+g*x (A+j) := by
        simpa only [Nat.add_assoc] using hr
      have hno := hodd' (a (A+j+1))
      change a (A+j+1)=a A
      rcases hz with hz0|hz1
      · rcases hb with hb0|hb1
        · rw [hp,hz0,hb0] at hp'; simp at hp'; omega
        · rw [hp,hz0,hb1] at hp'; simp at hp'; omega
      · rcases hb with hb0|hb1
        · rw [hp,hz1,hb0] at hp'; simp at hp'; omega
        · rw [hp,hz1,hb1] at hp'; simp at hp'; omega
  intro j hj
  have hp := h j (by omega)
  have hn := h (j+1) (by omega)
  have hr := hs (A+j) (by omega)
  have hno := hodd' (a (A+j+1))
  have hr' : 2*a (A+j+1)=a (A+j)+g*x (A+j) := by
    simpa only [Nat.add_assoc] using hr
  change a (A+j+1)=a A at hn
  rcases hz with hz0|hz1
  · simp [hz0]
    rw [hp,hz0,hn] at hr'
    have hb := hx (A+j) (by omega)
    rcases hb with hb0|hb1
    · exact hb0
    · rw [hb1] at hr'
      simp at hr'
      omega
  · have hnot : a A≠0 := by
      intro hzero
      have heq : g=0 := by omega
      omega
    simp [hnot]
    rw [hp,hz1,hn] at hr'
    have hb := hx (A+j) (by omega)
    rcases hb with hb0|hb1
    · rw [hb0] at hr'
      simp at hr'
      omega
    · exact hb1

/-- Any 2^r multiple of an odd h dividing 2^K+1, with coprime K,
    forbids a K-shift antiperiodic factor once the positive coordinates
    outlive their logarithmic capacity. -/
theorem no_scaled_negacyclic (h K A r B L : Nat) (q dir C g : Int)
    (a c w x : Nat→Int)
    (hh : 0<h) (hodd : (h:Int)%2=1) (hco : Nat.Coprime h K)
    (hmod : (h:Int)∣(2:Int)^K+1)
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
  apply no_coprime_negacyclic h K B (L-r-A) (q+dir*(A:Int)) dir
    (fun j => b (A+j)) (fun j => c (A+j)) (fun j => w (A+j)) (fun j => x (A+j))
    hh hco hmod hdir (by omega) hinner
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
  · have hci := hbound (A+K) (by omega)
    have hwi := hbound A (by omega)
    exact interior_energy_bound (h:Int) C (b A) (c (A+K)) (w A) dir K B
      (by omega) ⟨hci.1,hci.2.1,hwi.2.2.1,hwi.2.2.2⟩ hstart hdir hscale

#print axioms odd_boundary_lock
#print axioms no_scaled_negacyclic
end BB6.Agent9AntiGenericScaled
