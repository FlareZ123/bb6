import ReturnSlope

namespace BB6.Agent9ReturnGCD

/-- A sufficiently long positive bounded affine-clock path cannot
    support a confined odd integer slope of small magnitude. -/
theorem no_small_odd_slope (q dir C : Int) (g L B : Nat) (a c w x : Nat→Int)
    (hdir : dir=1∨dir= -1) (hg : g%2=1) (hL : 2*g+B≤L)
    (h0 : 0≤a 0 ∧ a 0≤(g:Int))
    (hx : ∀ j<L, x j=0∨x j=1)
    (hs : ∀ j<L, 2*c (j+1)=c j+(q+dir*(j:Int))*x j)
    (hw : ∀ j<L, x j=1 → 2*w (j+1)=w j)
    (ha : ∀ j<L, 2*a (j+1)=a j+(g:Int)*x j)
    (hbound : ∀ j≤L, 1≤c j ∧ c j≤C ∧ 1≤w j ∧ w j≤C)
    (hscale : (g:Int)*(C+(g:Int))<(2:Int)^B) : False := by
  have hgpos : 0<g := by omega
  have hgi : (g:Int)%2=1 := by omega
  have hC : 1≤C := by have := hbound 0 (by omega); omega
  have hCp : C<(2:Int)^B := by
    have h := Int.mul_le_mul_of_nonneg_right (show (1:Int)≤(g:Int) by omega) (show 0≤C+(g:Int) by omega)
    rw [Int.one_mul] at h
    omega
  by_cases hz : a 0=0
  · have hlock : ∀ j≤L, a j=0 := by
      intro j hj
      induction j with
      | zero => exact hz
      | succ j ih =>
        have h := ha j (by omega)
        rw [ih (by omega)] at h
        exact (odd_step_unique (g:Int) 0 (a (j+1)) 0 (x j) 0 hgi
          (hx j (by omega)) (Or.inl rfl) h (by simp)).1
    apply no_positive_halves c B
    · intro j hj
      have h := ha j (by omega)
      rw [hlock j (by omega),hlock (j+1) (by omega)] at h
      have hzero : x j=0 := by
        rcases hx j (by omega) with h0|h1
        · exact h0
        · rw [h1,Int.mul_one] at h; omega
      simpa [hzero] using hs j (by omega)
    · exact (hbound B (by omega)).1
    · exact Int.lt_of_le_of_lt (hbound 0 (by omega)).2.1 hCp
  by_cases hz' : a 0=(g:Int)
  · have hlock : ∀ j≤L, a j=(g:Int) := by
      intro j hj
      induction j with
      | zero => exact hz'
      | succ j ih =>
        have h := ha j (by omega)
        rw [ih (by omega)] at h
        exact (odd_step_unique (g:Int) (g:Int) (a (j+1)) (g:Int) (x j) 1 hgi
          (hx j (by omega)) (Or.inr rfl) h (by simp; omega)).1
    apply no_positive_halves w B
    · intro j hj
      have h := ha j (by omega)
      rw [hlock j (by omega),hlock (j+1) (by omega)] at h
      have hone : x j=1 := by
        rcases hx j (by omega) with h0|h1
        · rw [h0,Int.mul_zero] at h; omega
        · exact h1
      exact hw j (by omega) hone
    · exact (hbound B (by omega)).2.2.1
    · exact Int.lt_of_le_of_lt (hbound 0 (by omega)).2.2.2 hCp
  have hInt := slope_interior (g:Int) a x L (by omega) hx ha
  obtain ⟨p,hp,hpg,hret,hnd⟩ := slope_primitive_return g L a x hgpos (by omega) hInt hx ha
  have hper := slope_return_period (g:Int) a x L p hgi (by omega) hret hx ha
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
  let H : Nat→Int := fun j => (g:Int)*b j-(p:Int)*a j
  have hH : ∀ j<L-p, 2*H (j+1)=H j := by
    intro j hj
    dsimp [H]
    calc
      _ = (g:Int)*(2*b (j+1))-(p:Int)*(2*a (j+1)) := by
        rw [Int.mul_sub]; ac_rfl
      _ = (g:Int)*(b j+(p:Int)*x j)-(p:Int)*(a j+(g:Int)*x j) := by
        rw [hb j hj,ha j (by omega)]
      _ = _ := by
        simp only [Int.mul_add]
        rw [show (p:Int)*((g:Int)*x j)=(g:Int)*((p:Int)*x j) by ac_rfl]
        omega
  have hb0 : -C≤b 0 ∧ b 0≤C := by
    have h1 := hbound 0 (by omega)
    have h2 := hbound p (by omega)
    dsimp [b]
    rcases hdir with hdir|hdir <;> rw [hdir] <;> simp <;> omega
  have hbg1 := Int.mul_le_mul_of_nonneg_left hb0.1 (show 0≤(g:Int) by omega)
  have hbg2 := Int.mul_le_mul_of_nonneg_left hb0.2 (show 0≤(g:Int) by omega)
  rw [Int.mul_neg] at hbg1
  have hap1 := Int.mul_nonneg (show 0≤(p:Int) by omega) h0.1
  have hap2 := Int.mul_le_mul_of_nonneg_left h0.2 (show 0≤(p:Int) by omega)
  have hpg2 := Int.mul_le_mul_of_nonneg_right (show (p:Int)≤(g:Int) by omega) (show 0≤(g:Int) by omega)
  rw [Int.mul_add] at hscale
  have hH0 : H 0=0 := finite_half_zero H B (fun j hj => hH j (by omega)) (by dsimp [H]; omega)
  have hHz := halving_zero_all H (L-p) hH hH0
  have hbin : ∀ j<p, 0<b j ∧ b j<(p:Int) := by
    intro j hj
    have he := hHz j (by omega)
    dsimp [H] at he
    have haj := hInt j (by omega)
    have hm1 := Int.mul_pos (show 0<(p:Int) by omega) haj.1
    have hm2 := Int.mul_lt_mul_of_pos_left haj.2 (show 0<(p:Int) by omega)
    rw [Int.mul_comm (p:Int) (g:Int)] at hm2
    constructor
    · by_cases h : 0<b j
      · exact h
      · have hn := Int.mul_nonpos_of_nonneg_of_nonpos (show 0≤(g:Int) by omega) (show b j≤0 by omega)
        omega
    · by_cases h : b j<(p:Int)
      · exact h
      · have hn := Int.mul_le_mul_of_nonneg_left (show (p:Int)≤b j by omega) (show 0≤(g:Int) by omega)
        omega
  obtain ⟨i,j,hij,hjp,he⟩ := interior_collision b p hp hbin
  have h1 := hHz i (by omega)
  have h2 := hHz j (by omega)
  dsimp [H] at h1 h2
  rw [he] at h1
  have eq : (p:Int)*a i=(p:Int)*a j := by omega
  exact hnd i j hij hjp (Int.eq_of_mul_eq_mul_left (show (p:Int)≠0 by omega) eq)

#print axioms no_small_odd_slope

end BB6.Agent9ReturnGCD
