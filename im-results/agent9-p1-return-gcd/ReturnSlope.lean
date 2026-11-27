import ReturnGCD

namespace BB6.Agent9ReturnGCD

/-- Every integral affine slope already in [0,g] stays there. -/
theorem slope_interval (g : Int) (a x : Nat → Int) (L : Nat)
    (hg : 0≤g) (h0 : 0≤a 0 ∧ a 0≤g)
    (hx : ∀ j<L, x j=0 ∨ x j=1)
    (hs : ∀ j<L, 2*a (j+1)=a j+g*x j) :
    ∀ j≤L, 0≤a j ∧ a j≤g := by
  intro j hj
  induction j with
  | zero => exact h0
  | succ j ih =>
    have ha := ih (by omega)
    have h := hs j (by omega)
    rcases hx j (by omega) with h0|h1
    · rw [h0] at h
      simp at h
      omega
    · rw [h1] at h
      simp at h
      omega

/-- At odd g the next slope and its bit are uniquely determined. -/
theorem odd_step_unique (g a b c x y : Int) (hg : g%2=1)
    (hx : x=0 ∨ x=1) (hy : y=0 ∨ y=1)
    (hb : 2*b=a+g*x) (hc : 2*c=a+g*y) : b=c ∧ x=y := by
  rcases hx with hx|hx <;> rcases hy with hy|hy <;>
    rw [hx] at hb <;> rw [hy] at hc <;> simp at hb hc <;> omega

/-- A nonconstant odd slope remains strictly interior. -/
theorem slope_interior (g : Int) (a x : Nat → Int) (L : Nat)
    (h0 : 0<a 0 ∧ a 0<g)
    (hx : ∀ j<L, x j=0 ∨ x j=1)
    (hs : ∀ j<L, 2*a (j+1)=a j+g*x j) :
    ∀ j≤L, 0<a j ∧ a j<g := by
  intro j hj
  induction j with
  | zero => exact h0
  | succ j ih =>
    have ha := ih (by omega)
    have h := hs j (by omega)
    rcases hx j (by omega) with h0|h1
    · rw [h0] at h
      simp at h
      omega
    · rw [h1] at h
      simp at h
      omega

/-- The earlier slope is also uniquely determined if both are interior. -/
theorem interior_prev_unique (g a b c x y : Int)
    (ha : 0<a ∧ a<g) (hb : 0<b ∧ b<g)
    (hx : x=0 ∨ x=1) (hy : y=0 ∨ y=1)
    (h1 : 2*c=a+g*x) (h2 : 2*c=b+g*y) : a=b := by
  rcases hx with hx|hx <;> rcases hy with hy|hy <;>
    rw [hx] at h1 <;> rw [hy] at h2 <;> simp at h1 h2 <;> omega

/-- Pigeonhole principle for p integers strictly between 0 and p. -/
theorem interior_collision (f : Nat → Int) (p : Nat) (hp : 0<p)
    (hb : ∀ j<p, 0<f j ∧ f j<(p:Int)) :
    ∃ i j, i<j ∧ j<p ∧ f i=f j := by
  by_cases h : ∃ i j, i<j ∧ j<p ∧ f i=f j
  · exact h
  · exfalso
    let g : Nat → Nat := fun i => (f i).toNat
    have hnd : ((List.range p).map g).Nodup := by
      rw [List.nodup_iff_pairwise_ne,List.pairwise_map,List.pairwise_iff_getElem]
      intro i j hi hj hij
      simp only [List.getElem_range]
      intro he
      have hdi := Int.toNat_of_nonneg (show 0≤f i by have := (hb i (by simpa using hi)).1; omega)
      have hdj := Int.toNat_of_nonneg (show 0≤f j by have := (hb j (by simpa using hj)).1; omega)
      have he' : f i=f j := by
        change (f i).toNat=(f j).toNat at he
        omega
      exact h ⟨i,j,hij,by simpa using hj,he'⟩
    have hsub : (List.range p).map g ⊆ List.range' 1 (p-1) := by
      intro a ha
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
      have hi' := List.mem_range.mp hi
      have hb' := hb i hi'
      have hcast := Int.toNat_of_nonneg (show 0≤f i by omega)
      have hf : 0<g i ∧ g i<p := by dsimp [g]; omega
      apply List.mem_range'.2
      exact ⟨g i-1,by omega,by omega⟩
    have hlen := hnd.length_le_of_subset hsub
    simp only [List.length_map,List.length_range,List.length_range'] at hlen
    omega

private theorem back_to_zero (g : Int) (a x : Nat → Int) (L p : Nat)
    (hb : ∀ j≤L, 0<a j ∧ a j<g)
    (hx : ∀ j<L, x j=0 ∨ x j=1)
    (hs : ∀ j<L, 2*a (j+1)=a j+g*x j) :
    ∀ i, i+p≤L → a i=a (i+p) → a 0=a p := by
  intro i
  induction i with
  | zero => intro _ h; simpa using h
  | succ i ih =>
    intro hi he
    have h1 := hs i (by omega)
    have h2 := hs (i+p) (by omega)
    rw [show i+p+1=i+1+p by omega,←he] at h2
    have h := interior_prev_unique g (a i) (a (i+p)) (a (i+1)) (x i) (x (i+p))
      (hb i (by omega)) (hb (i+p) (by omega))
      (hx i (by omega)) (hx (i+p) (by omega)) h1 h2
    exact ih (by omega) h

/-- A finite interior slope has a primitive return of length <g, even
    without assuming its original carry word periodic. -/
theorem slope_primitive_return (g L : Nat) (a x : Nat → Int)
    (hg : 0<g) (hL : g≤L)
    (hb : ∀ j≤L, 0<a j ∧ a j<(g:Int))
    (hx : ∀ j<L, x j=0 ∨ x j=1)
    (hs : ∀ j<L, 2*a (j+1)=a j+(g:Int)*x j) :
    ∃ p, 0<p ∧ p<g ∧ a p=a 0 ∧
      (∀ i j, i<j → j<p → a i≠a j) := by
  obtain ⟨i,j,hij,hjg,he⟩ := interior_collision a g hg (fun j hj => hb j (by omega))
  let k := j-i
  have hk : 0<k := by dsimp [k]; omega
  have hkg : k<g := by dsimp [k]; omega
  have hret : a k=a 0 := by
    have h := back_to_zero (g:Int) a x L k hb hx hs i
      (by dsimp [k]; omega) (by rwa [show i+k=j by dsimp [k]; omega])
    exact h.symm
  have hmin : ∀ k, 0<k → k<g → a k=a 0 →
      ∃ p, 0<p ∧ p<g ∧ a p=a 0 ∧
        (∀ t, 0<t → t<p → a t≠a 0) := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro hk hkg hr
      by_cases h : ∃ t, 0<t ∧ t<k ∧ a t=a 0
      · obtain ⟨t,ht,htk,he⟩ := h
        exact ih t htk ht (by omega) he
      · refine ⟨k,hk,hkg,hr,?_⟩
        intro t ht htk he
        exact h ⟨t,ht,htk,he⟩
  obtain ⟨p,hp,hpg,hr,hm⟩ := hmin k hk hkg hret
  refine ⟨p,hp,hpg,hr,?_⟩
  intro i j hij hjp he
  let r := j-i
  have h0 : a 0=a r := back_to_zero (g:Int) a x L r hb hx hs i
    (by dsimp [r]; omega) (by rwa [show i+r=j by dsimp [r]; omega])
  exact hm r (by dsimp [r]; omega) (by dsimp [r]; omega) h0.symm

/-- An odd slope return forces the subsequent bits to repeat. -/
theorem slope_return_period (g : Int) (a x : Nat → Int) (L p : Nat)
    (hg : g%2=1) (_hp : p≤L) (hret : a p=a 0)
    (hx : ∀ j<L, x j=0 ∨ x j=1)
    (hs : ∀ j<L, 2*a (j+1)=a j+g*x j) :
    ∀ j, j+p<L → x (j+p)=x j := by
  have ha : ∀ j, j+p≤L → a (j+p)=a j := by
    intro j
    induction j with
    | zero => intro _; simpa using hret
    | succ j ih =>
      intro hj
      have h1 := hs j (by omega)
      have h2 := hs (j+p) (by omega)
      rw [ih (by omega)] at h2
      have h := odd_step_unique g (a j) (a (j+p+1)) (a (j+1)) (x (j+p)) (x j)
        hg (hx (j+p) (by omega)) (hx j (by omega)) h2 h1
      simpa only [show j+1+p=j+p+1 by omega] using h.1
  intro j hj
  have h1 := hs j (by omega)
  have h2 := hs (j+p) (by omega)
  rw [ha j (by omega)] at h2
  exact (odd_step_unique g (a j) (a (j+p+1)) (a (j+1)) (x (j+p)) (x j)
    hg (hx (j+p) (by omega)) (hx j (by omega)) h2 h1).2

/-- A vanishing half-difference is forced by enough integral steps. -/
theorem finite_half_zero (f : Nat → Int) (L : Nat)
    (hs : ∀ j<L, 2*f (j+1)=f j)
    (hb : -(2:Int)^L < f 0 ∧ f 0 < (2:Int)^L) :
    f 0=0 := by
  have h := growth f L (fun j hj => by have := hs j hj; omega)
  have hn := growth (fun j => -f j) L (fun j hj => by have := hs j hj; omega)
  change -f 0≤(2:Int)^L*(-f L) at hn
  rw [Int.mul_neg] at hn
  have he : f 0=(2:Int)^L*f L := by omega
  have hp : 0≤(2:Int)^L := Int.pow_nonneg (by decide : 0≤(2:Int))
  by_cases h0 : f L=0
  · rw [h0,Int.mul_zero] at he
    exact he
  · by_cases hpos : 0<f L
    · have hm := Int.mul_le_mul_of_nonneg_left (show 1≤f L by omega) hp
      rw [Int.mul_one] at hm
      omega
    · have hm := Int.mul_le_mul_of_nonneg_left (show f L≤ -1 by omega) hp
      simp only [Int.mul_neg,Int.mul_one] at hm
      omega

theorem halving_zero_all (f : Nat → Int) (L : Nat)
    (hs : ∀ j<L, 2*f (j+1)=f j) (h0 : f 0=0) :
    ∀ j≤L, f j=0 := by
  intro j hj
  induction j with
  | zero => exact h0
  | succ j ih =>
    have h := hs j (by omega)
    rw [ih (by omega)] at h
    omega

#print axioms slope_primitive_return
#print axioms slope_return_period
#print axioms finite_half_zero

end BB6.Agent9ReturnGCD
