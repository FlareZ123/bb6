import ReturnSlope
namespace BB6.Agent43OrderReturn
open BB6.Agent9ReturnGCD

/-- Unroll a fixed integer slope for any number of bits. -/
theorem affine_dvd (g : Int) (a x : Nat → Int) (K : Nat)
    (ha : ∀ j<K, 2*a (j+1)=a j+g*x j) :
    ∃ t : Int, (2:Int)^K*a K=a 0+g*t := by
  induction K with
  | zero => exact ⟨0,by simp⟩
  | succ K ih =>
    obtain ⟨t,ht⟩ := ih (fun j hj => ha j (by omega))
    refine ⟨t+(2:Int)^K*x K,?_⟩
    calc
      _ = (2:Int)^K*(2*a (K+1)) := by rw [Int.pow_succ]; ac_rfl
      _ = (2:Int)^K*(a K+g*x K) := by rw [ha K (by omega)]
      _ = a 0+g*(t+(2:Int)^K*x K) := by
        rw [Int.mul_add,ht,Int.mul_add]
        rw [show (2:Int)^K*(g*x K)=g*((2:Int)^K*x K) by ac_rfl]
        omega

/-- A supplied multiplicative-order multiple forces an actual return of the
    confined interior slope. The modulus may be exponentially larger than K. -/
theorem order_return (g : Int) (a x : Nat → Int) (K : Nat)
    (ho : g ∣ (2:Int)^K-1)
    (h0 : 0<a 0 ∧ a 0<g) (hK : 0<a K ∧ a K<g)
    (ha : ∀ j<K, 2*a (j+1)=a j+g*x j) : a K=a 0 := by
  obtain ⟨t,ht⟩ := affine_dvd g a x K ha
  obtain ⟨u,hu⟩ := ho
  have he : (2:Int)^K=1+g*u := by omega
  rw [he,Int.add_mul,Int.one_mul,Int.mul_assoc] at ht
  have hh : a K-a 0=g*(t-u*a K) := by rw [Int.mul_sub]; omega
  by_cases hz : t-u*a K=0
  · rw [hz,Int.mul_zero] at hh; omega
  · by_cases hp : 0<t-u*a K
    · have hm := Int.mul_le_mul_of_nonneg_left (show 1≤t-u*a K by omega) (show 0≤g by omega)
      rw [Int.mul_one] at hm; omega
    · have hm := Int.mul_le_mul_of_nonneg_left (show t-u*a K≤ -1 by omega) (show 0≤g by omega)
      simp only [Int.mul_neg,Int.mul_one] at hm; omega

/-- From any return, extract the primitive return, without assuming that
    the finite word extends indefinitely. -/
theorem primitive_of_return (g : Int) (a x : Nat → Int) (L K : Nat)
    (hK : 0<K) (hKL : K≤L) (hret : a K=a 0)
    (hb : ∀ j≤L, 0<a j ∧ a j<g)
    (hx : ∀ j<L, x j=0∨x j=1)
    (ha : ∀ j<L, 2*a (j+1)=a j+g*x j) :
    ∃ p, 0<p ∧ p≤K ∧ a p=a 0 ∧ (∀ i j, i<j → j<p → a i≠a j) := by
  have hmin : ∀ k, 0<k → a k=a 0 →
      ∃ p, 0<p ∧ p≤k ∧ a p=a 0 ∧ (∀ t, 0<t → t<p → a t≠a 0) := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro hk hr
      by_cases h : ∃ t, 0<t ∧ t<k ∧ a t=a 0
      · obtain ⟨t,ht,htk,he⟩ := h
        obtain ⟨p,hp,hpt,hpr,hm⟩ := ih t htk ht he
        exact ⟨p,hp,by omega,hpr,hm⟩
      · exact ⟨k,hk,by omega,hr,fun t ht htk he => h ⟨t,ht,htk,he⟩⟩
  obtain ⟨p,hp,hpk,hpr,hm⟩ := hmin K hK hret
  refine ⟨p,hp,hpk,hpr,?_⟩
  intro i j hij hjp he
  let r := j-i
  have hback : ∀ t, t+r≤L → a t=a (t+r) → a 0=a r := by
    intro t
    induction t with
    | zero => intro _ h; simpa using h
    | succ t ih =>
      intro ht h
      have h1 := ha t (by omega)
      have h2 := ha (t+r) (by omega)
      rw [show t+r+1=t+1+r by omega,←h] at h2
      have he' := interior_prev_unique g (a t) (a (t+r)) (a (t+1)) (x t) (x (t+r))
        (hb t (by omega)) (hb (t+r) (by omega)) (hx t (by omega)) (hx (t+r) (by omega)) h1 h2
      exact ih (by omega) he'
  have he' := hback i (by dsimp [r]; omega) (by rwa [show i+r=j by dsimp [r]; omega])
  exact hm r (by dsimp [r]; omega) (by dsimp [r]; omega) he'.symm

private theorem half_return_zero (f : Nat → Int) (p : Nat) (hp : 0<p)
    (hf : ∀ j<p, 2*f (j+1)=f j) (hret : f p=f 0) : f 0=0 := by
  have h := growth f p (fun j hj => by have := hf j hj; omega)
  have hn := growth (fun j => -f j) p (fun j hj => by have := hf j hj; omega)
  change -f 0≤(2:Int)^p*(-f p) at hn
  rw [Int.mul_neg] at hn
  have he : f 0=(2:Int)^p*f p := by omega
  rw [hret] at he
  have hm : ((2:Int)^p-1)*f 0=0 := by rw [Int.sub_mul,Int.one_mul]; omega
  have hpow : 1<(2:Int)^p := by
    cases p with
    | zero => omega
    | succ p => rw [Int.pow_succ]; have hpos : 0<(2:Int)^p := Int.pow_pos (by decide); omega
  rcases Int.mul_eq_zero.mp hm with h0|h0
  · omega
  · exact h0

/-- A bounded affine-clock word with an odd slope whose doubling order
    divides K cannot survive 2K+B bits when 2C<2^B. The bound depends on the
    order, not the magnitude of the odd slope. The determinant is killed by
    a periodic return rather than by a magnitude bound on its coefficients. -/
theorem no_bounded_return_slope (q dir C g : Int) (K L B : Nat) (a c w x : Nat→Int)
    (hdir : dir=1∨dir= -1) (hg : g%2=1)
    (hreturn : 0<a 0 ∧ a 0<g → ∃ k, 0<k ∧ k≤K ∧ a k=a 0) (hL : 2*K+B≤L)
    (h0 : 0≤a 0 ∧ a 0≤g)
    (hx : ∀ j<L, x j=0∨x j=1)
    (hs : ∀ j<L, 2*c (j+1)=c j+(q+dir*(j:Int))*x j)
    (hw : ∀ j<L, x j=1 → 2*w (j+1)=w j)
    (ha : ∀ j<L, 2*a (j+1)=a j+g*x j)
    (hbound : ∀ j≤L, 1≤c j ∧ c j≤C ∧ 1≤w j ∧ w j≤C)
    (hscale : 2*C<(2:Int)^B) : False := by
  have hgpos : 0<g := by omega
  have hC : 1≤C := by have := hbound 0 (by omega); omega
  have hCp : C<(2:Int)^B := by omega
  by_cases hz : a 0=0
  · have hlock : ∀ j≤L, a j=0 := by
      intro j hj
      induction j with
      | zero => exact hz
      | succ j ih =>
        have h := ha j (by omega)
        rw [ih (by omega)] at h
        exact (odd_step_unique g 0 (a (j+1)) 0 (x j) 0 hg
          (hx j (by omega)) (Or.inl rfl) h (by simp)).1
    apply no_positive_halves c B
    · intro j hj
      have h := ha j (by omega)
      rw [hlock j (by omega),hlock (j+1) (by omega)] at h
      have he : x j=0 := by rcases hx j (by omega) with h0|h1; exact h0; rw [h1,Int.mul_one] at h; omega
      simpa [he] using hs j (by omega)
    · exact (hbound B (by omega)).1
    · exact Int.lt_of_le_of_lt (hbound 0 (by omega)).2.1 hCp
  by_cases hz' : a 0=g
  · have hlock : ∀ j≤L, a j=g := by
      intro j hj
      induction j with
      | zero => exact hz'
      | succ j ih =>
        have h := ha j (by omega)
        rw [ih (by omega)] at h
        exact (odd_step_unique g g (a (j+1)) g (x j) 1 hg
          (hx j (by omega)) (Or.inr rfl) h (by simp; omega)).1
    apply no_positive_halves w B
    · intro j hj
      have h := ha j (by omega)
      rw [hlock j (by omega),hlock (j+1) (by omega)] at h
      have he : x j=1 := by rcases hx j (by omega) with h0|h1; rw [h0,Int.mul_zero] at h; omega; exact h1
      exact hw j (by omega) he
    · exact (hbound B (by omega)).2.2.1
    · exact Int.lt_of_le_of_lt (hbound 0 (by omega)).2.2.2 hCp
  have hint := slope_interior g a x L (by omega) hx ha
  obtain ⟨k,hk,hkK,hret⟩ := hreturn (by omega)
  obtain ⟨p,hp,hpk,hpr,hnd⟩ := primitive_of_return g a x L k hk (by omega) hret hint hx ha
  have hper := slope_return_period g a x L p hg (by omega) hpr hx ha
  let b : Nat→Int := fun j => dir*(c (j+p)-c j)
  have hb : ∀ j<L-p, 2*b (j+1)=b j+(p:Int)*x j := by
    intro j hj
    have h1 := hs j (by omega)
    have h2 := hs (j+p) (by omega)
    rw [hper j (by omega)] at h2
    dsimp [b]
    rw [show j+1+p=j+p+1 by omega]
    rcases hdir with hdir|hdir <;> rw [hdir] at h1 h2 ⊢ <;>
      rcases hx j (by omega) with hbit|hbit <;> rw [hbit] at h1 h2 ⊢ <;>
      simp at h1 h2 ⊢ <;> omega
  let e : Nat→Int := fun j => b (j+p)-b j
  have he : ∀ j<B, 2*e (j+1)=e j := by
    intro j hj
    have h1 := hb j (by omega)
    have h2 := hb (j+p) (by omega)
    rw [hper j (by omega)] at h2
    dsimp [e]
    rw [show j+1+p=j+p+1 by omega]
    omega
  have heB : -(2:Int)^B<e 0 ∧ e 0<(2:Int)^B := by
    have h0 := hbound 0 (by omega)
    have h1 := hbound p (by omega)
    have h2 := hbound (p+p) (by omega)
    simp only [e,b,Nat.zero_add]
    rcases hdir with h|h <;> rw [h] <;> simp <;> omega
  have he0 := finite_half_zero e B he heB
  have hbp : b p=b 0 := by simp only [e,Nat.zero_add] at he0; omega
  let H : Nat→Int := fun j => g*b j-(p:Int)*a j
  have hH : ∀ j<p, 2*H (j+1)=H j := by
    intro j hj
    dsimp [H]
    calc
      _ = g*(2*b (j+1))-(p:Int)*(2*a (j+1)) := by rw [Int.mul_sub]; ac_rfl
      _ = g*(b j+(p:Int)*x j)-(p:Int)*(a j+g*x j) := by rw [hb j (by omega),ha j (by omega)]
      _ = _ := by
        simp only [Int.mul_add]
        rw [show (p:Int)*(g*x j)=g*((p:Int)*x j) by ac_rfl]
        omega
  have hHp : H p=H 0 := by simp only [H,hbp,hpr]
  have hH0 := half_return_zero H p hp hH hHp
  have hHz := halving_zero_all H p hH hH0
  have hbin : ∀ j<p, 0<b j ∧ b j<(p:Int) := by
    intro j hj
    have he := hHz j (by omega)
    dsimp [H] at he
    have haj := hint j (by omega)
    have hm1 := Int.mul_pos (show 0<(p:Int) by omega) haj.1
    have hm2 := Int.mul_lt_mul_of_pos_left haj.2 (show 0<(p:Int) by omega)
    rw [Int.mul_comm (p:Int) g] at hm2
    constructor
    · by_cases h : 0<b j
      · exact h
      · have hn := Int.mul_nonpos_of_nonneg_of_nonpos (show 0≤g by omega) (show b j≤0 by omega)
        omega
    · by_cases h : b j<(p:Int)
      · exact h
      · have hn := Int.mul_le_mul_of_nonneg_left (show (p:Int)≤b j by omega) (show 0≤g by omega)
        omega
  obtain ⟨i,j,hij,hjp,he⟩ := interior_collision b p hp hbin
  have h1 := hHz i (by omega)
  have h2 := hHz j (by omega)
  dsimp [H] at h1 h2
  rw [he] at h1
  have eq : (p:Int)*a i=(p:Int)*a j := by omega
  exact hnd i j hij hjp (Int.eq_of_mul_eq_mul_left (show (p:Int)≠0 by omega) eq)

/-- Multiplicative order supplies the bounded-return premise directly. -/
theorem no_short_order_slope (q dir C g : Int) (K L B : Nat) (a c w x : Nat→Int)
    (hdir : dir=1∨dir= -1) (hg : g%2=1) (hK : 0<K)
    (ho : g ∣ (2:Int)^K-1) (hL : 2*K+B≤L)
    (h0 : 0≤a 0 ∧ a 0≤g)
    (hx : ∀ j<L, x j=0∨x j=1)
    (hs : ∀ j<L, 2*c (j+1)=c j+(q+dir*(j:Int))*x j)
    (hw : ∀ j<L, x j=1 → 2*w (j+1)=w j)
    (ha : ∀ j<L, 2*a (j+1)=a j+g*x j)
    (hbound : ∀ j≤L, 1≤c j ∧ c j≤C ∧ 1≤w j ∧ w j≤C)
    (hscale : 2*C<(2:Int)^B) : False := by
  apply no_bounded_return_slope q dir C g K L B a c w x hdir hg _ hL h0 hx hs hw ha hbound hscale
  intro hi
  have hb := slope_interior g a x L hi hx ha
  exact ⟨K,hK,Nat.le_refl _,order_return g a x K ho hi (hb K (by omega)) (fun j hj => ha j (by omega))⟩

/-- Even without a supplied order, the interior-slope pigeonhole bound
    can use the smaller 2C<2^B threshold. -/
theorem no_small_slope_sharp (q dir C : Int) (g L B : Nat) (a c w x : Nat→Int)
    (hdir : dir=1∨dir= -1) (hg : g%2=1) (hL : 2*g+B≤L)
    (h0 : 0≤a 0 ∧ a 0≤(g:Int))
    (hx : ∀ j<L, x j=0∨x j=1)
    (hs : ∀ j<L, 2*c (j+1)=c j+(q+dir*(j:Int))*x j)
    (hw : ∀ j<L, x j=1 → 2*w (j+1)=w j)
    (ha : ∀ j<L, 2*a (j+1)=a j+(g:Int)*x j)
    (hbound : ∀ j≤L, 1≤c j ∧ c j≤C ∧ 1≤w j ∧ w j≤C)
    (hscale : 2*C<(2:Int)^B) : False := by
  apply no_bounded_return_slope q dir C (g:Int) g L B a c w x hdir (by omega) _ hL h0 hx hs hw ha hbound hscale
  intro hi
  have hb := slope_interior (g:Int) a x L hi hx ha
  obtain ⟨p,hp,hpg,hret,_⟩ := slope_primitive_return g L a x (by omega) (by omega) hb hx ha
  exact ⟨p,hp,by omega,hret⟩

#print axioms order_return
#print axioms primitive_of_return
#print axioms no_bounded_return_slope
#print axioms no_short_order_slope
#print axioms no_small_slope_sharp
end BB6.Agent43OrderReturn
