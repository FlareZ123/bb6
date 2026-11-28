import CyclicOrder
import OrderReturn
set_option maxHeartbeats 0

namespace BB6.Agent9CyclicShort
open BB6.Agent9ReturnGCD BB6.Agent9AntiGenericBound BB6.Agent43OrderReturn

/-- A bounded positive affine-clock carry cannot have a repeated
    interior odd slope of (not necessarily coprime) modulus h once its
    return is at most K and the logarithmic coordinate margin B is at
    least K. The mixed determinant after the primitive return p uses
    only p+B steps, rather than the older 2p+B second-difference bound. -/
theorem no_short_return_carry
    (q dir C g : Int) (K B L : Nat) (a c x : Nat → Int)
    (hdir : dir=1 ∨ dir= -1) (hodd : g%2=1)
    (hret : 0<a 0 ∧ a 0<g →
      ∃ k, 0<k ∧ k≤K ∧ a k=a 0)
    (hKL : K+B≤L) (hBK : K≤B)
    (hinside : ∀ j≤L, 0<a j ∧ a j<g)
    (hx : ∀ j<L, x j=0 ∨ x j=1)
    (ha : ∀ j<L, 2*a (j+1)=a j+g*x j)
    (hc : ∀ j<L, 2*c (j+1)=c j+(q+dir*(j:Int))*x j)
    (hbound : ∀ j≤L, 1≤c j ∧ c j≤C)
    (hscale : g*(C+(K:Int)+1)<(2:Int)^B) : False := by
  have hg : 0<g := by have hh := hinside 0 (by omega); omega
  obtain ⟨k,hk,hkK,hreturn⟩ := hret (hinside 0 (by omega))
  obtain ⟨p,hp,hpk,hpr,hnd⟩ := primitive_of_return
    g a x L k hk (by omega) hreturn hinside hx ha
  have hpK : p≤K := by omega
  have hpB : p≤B := by omega
  have hper := slope_return_period g a x L p hodd
    (by omega) hpr hx ha
  let b : Nat → Int := fun j => dir*(c (j+p)-c j)
  have hb : ∀ j<L-p, 2*b (j+1)=b j+(p:Int)*x j := by
    intro j hj
    have h1 := hc j (by omega)
    have h2 := hc (j+p) (by omega)
    rw [hper j (by omega)] at h2
    dsimp [b]
    rw [show j+1+p=j+p+1 by omega]
    rcases hdir with hdir|hdir <;> rw [hdir] at h1 h2 ⊢ <;>
      rcases hx j (by omega) with hbit|hbit <;> rw [hbit] at h1 h2 ⊢ <;>
      simp at h1 h2 ⊢ <;> omega
  let E : Nat → Int := fun j => g*b j-(p:Int)*a j
  have hhalf : ∀ j<B, 2*E (j+1)=E j := by
    intro j hj
    have hs := hb j (by omega)
    have hh := ha j (by omega)
    dsimp [E]
    calc
      2*(g*b (j+1)-(p:Int)*a (j+1)) =
          g*(2*b (j+1))-(p:Int)*(2*a (j+1)) := by
        simp only [Int.mul_sub,Int.mul_assoc]
        ac_rfl
      _ = g*(b j+(p:Int)*x j)-
            (p:Int)*(a j+g*x j) := by rw [hs,hh]
      _ = g*b j-(p:Int)*a j := by
        simp only [Int.mul_add,Int.mul_sub]
        have heq : g*((p:Int)*x j)=(p:Int)*(g*x j) := by ac_rfl
        rw [heq]
        omega
  have hscaleP : g*(C+(p:Int)+1)<(2:Int)^B := by
    have hp : C+(p:Int)+1≤C+(K:Int)+1 := by omega
    have hm := Int.mul_le_mul_of_nonneg_left hp (by omega : 0≤g)
    exact lt_of_le_of_lt hm hscale
  have hEbound : -(2:Int)^B<E 0 ∧ E 0<(2:Int)^B := by
    have hpos : 0<g-a 0 ∧ g-a 0<g := by
      have hh := hinside 0 (by omega)
      omega
    rcases hdir with hd|hd
    · have hi := interior_energy_bound g C (g-a 0)
        (c p) (c 0) 1 p B hg
        ⟨(hbound p (by omega)).1,(hbound p (by omega)).2,
          (hbound 0 (by omega)).1,(hbound 0 (by omega)).2⟩
        hpos (Or.inl rfl) hscaleP
      have heq : g*(c p-c 0)+(1:Int)*(p:Int)*(g-a 0)-
        (1:Int)*(p:Int)*g=E 0 := by
        simp only [E,b,Nat.zero_add,hd,Int.one_mul,Int.mul_sub]
        omega
      rw [heq] at hi
      exact hi
    · have hi := interior_energy_bound g C (g-a 0)
        (c 0) (c p) 1 p B hg
        ⟨(hbound 0 (by omega)).1,(hbound 0 (by omega)).2,
          (hbound p (by omega)).1,(hbound p (by omega)).2⟩
        hpos (Or.inl rfl) hscaleP
      have heq : g*(c 0-c p)+(1:Int)*(p:Int)*(g-a 0)-
        (1:Int)*(p:Int)*g=E 0 := by
        simp only [E,b,Nat.zero_add,hd,Int.one_mul,Int.mul_sub,
          Int.mul_assoc,Int.neg_one_mul]
        omega
      rw [heq] at hi
      exact hi
  have hE0 := finite_half_zero E B hhalf hEbound
  have hEz := halving_zero_all E p
    (fun j hj => hhalf j (by omega)) hE0
  have hbin : ∀ j<p, 0<b j ∧ b j<(p:Int) := by
    intro j hj
    have he := hEz j (by omega)
    dsimp [E] at he
    have haj := hinside j (by omega)
    have hm1 := Int.mul_pos (show 0<(p:Int) by omega) haj.1
    have hm2 := Int.mul_lt_mul_of_pos_left haj.2
      (show 0<(p:Int) by omega)
    rw [Int.mul_comm (p:Int) g] at hm2
    constructor
    · by_cases h : 0<b j
      · exact h
      · have hn := Int.mul_nonpos_of_nonneg_of_nonpos
          (show 0≤g by omega) (show b j≤0 by omega)
        omega
    · by_cases h : b j<(p:Int)
      · exact h
      · have hn := Int.mul_le_mul_of_nonneg_left
          (show (p:Int)≤b j by omega) (show 0≤g by omega)
        omega
  obtain ⟨i,j,hij,hjp,he⟩ := interior_collision b p hp hbin
  have h1 := hEz i (by omega)
  have h2 := hEz j (by omega)
  dsimp [E] at h1 h2
  rw [he] at h1
  have eq : (p:Int)*a i=(p:Int)*a j := by omega
  exact hnd i j hij hjp
    (Int.eq_of_mul_eq_mul_left (show (p:Int)≠0 by omega) eq)

/-- Supplied Mersenne order K is a short return bound; this covers all
    odd h, even when gcd(h,K)>1. -/
theorem no_short_mersenne
    (q dir C h : Int) (K B L : Nat)
    (a c x : Nat → Int)
    (hdir : dir=1 ∨ dir= -1) (hodd : h%2=1)
    (hK : 0<K) (horder : h∣(2:Int)^K-1)
    (hKL : K+B≤L) (hBK : K≤B)
    (hinside : ∀ j≤L, 0<a j ∧ a j<h)
    (hx : ∀ j<L, x j=0 ∨ x j=1)
    (ha : ∀ j<L, 2*a (j+1)=a j+h*x j)
    (hc : ∀ j<L, 2*c (j+1)=c j+(q+dir*(j:Int))*x j)
    (hbound : ∀ j≤L, 1≤c j ∧ c j≤C)
    (hscale : h*(C+(K:Int)+1)<(2:Int)^B) : False := by
  apply no_short_return_carry q dir C h K B L a c x
    hdir hodd _ hKL hBK hinside hx ha hc hbound hscale
  intro hi
  have hKI := hinside K (by omega)
  exact ⟨K,hK,Nat.le_refl _,
    order_return h a x K horder hi hKI
      (fun j hj => ha j (by omega))⟩

/-- Shortened positive-clock obstruction under a supplied Mersenne order.
    Unlike the coprime-only obstruction, this accepts any odd h if K≤B.
    The extra r positions remove the dyadic part of the original slope. -/
theorem no_scaled_short
    (h K A r B L : Nat) (q dir C g : Int)
    (a c w x : Nat → Int)
    (hh : 0<h) (hodd : (h:Int)%2=1)
    (horder : (h:Int)∣(2:Int)^K-1)
    (hK : 0<K) (hKB : K≤B)
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
  apply no_short_mersenne (q+dir*(A:Int)) dir C (h:Int) K B (L-r-A)
    (fun j => b (A+j)) (fun j => c (A+j))
    (fun j => x (A+j))
    hdir hodd hK horder (by omega) hKB hinner
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

#print axioms no_short_return_carry
#print axioms no_short_mersenne
#print axioms no_scaled_short
end BB6.Agent9CyclicShort
