import BB429PeriodicDynamics

namespace BB429.PeriodicHigh

def IsPeriod (e : Nat → Bool) (l : Nat) : Prop := 0<l ∧ ∀ n,e (n+l)=e n

theorem least_period (e : Nat → Bool) (l : Nat) (h : IsPeriod e l) :
    ∃ m, IsPeriod e m ∧ ∀ k, IsPeriod e k → m≤k := by
  induction l using Nat.strongRecOn with
  | ind l ih =>
    by_cases hsmall : ∃ k<l, IsPeriod e k
    · obtain ⟨k,hk,hper⟩ := hsmall
      exact ih k hk hper
    · refine ⟨l,h,?_⟩
      intro k hk
      by_cases hh : k<l
      · exact False.elim (hsmall ⟨k,hh,hk⟩)
      · omega

theorem period_mul (e : Nat → Bool) (l : Nat) (h : ∀ n,e (n+l)=e n) :
    ∀ n k,e (n+l*k)=e n := by
  intro n k
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ,← Nat.add_assoc,h,ih]

theorem period_reduce (e : Nat → Bool) (l : Nat) (h : IsPeriod e l) (n : Nat) :
    e n=e (n%l) := by
  have hh := Nat.mod_add_div n l
  conv => lhs; rw [← hh]
  exact period_mul e l h.2 _ _

/-- Minimal positive period entails pairwise distinct digit rotations. -/
theorem least_period_primitive (e : Nat → Bool) (l : Nat) (h : IsPeriod e l)
    (hmin : ∀ k, IsPeriod e k → l≤k) :
    ∀ i j,i<l → j<l → i≠j → ∃ k,e (i+k)≠e (j+k) := by
  have hordered : ∀ i j,i<j → j<l → ∃ k,e (i+k)≠e (j+k) := by
    intro i j hij hj
    by_cases hne : ∃ k,e (i+k)≠e (j+k)
    · exact hne
    exfalso
    have hs : ∀ k,e (i+k)=e (j+k) := by
      intro k
      by_cases hh : e (i+k)=e (j+k)
      · exact hh
      · exact False.elim (hne ⟨k,hh⟩)
    let d := j-i
    have hd : IsPeriod e d := by
      refine ⟨by dsimp [d]; omega,?_⟩
      intro n
      have hmul := Nat.mul_le_mul_right i (show 1≤l by have hh:=h.1; omega)
      simp at hmul
      let k := n+l*i-i
      have hi : i+k=n+l*i := by dsimp [k]; omega
      have hj' : j+k=n+d+l*i := by dsimp [k,d]; omega
      have hh := hs k
      rw [hi,hj',period_mul e l h.2,period_mul e l h.2] at hh
      exact hh.symm
    have hh := hmin d hd
    dsimp [d] at hh
    omega
  intro i j hi hj hij
  by_cases hij' : i<j
  · exact hordered i j hij' hj
  · obtain ⟨k,hk⟩ := hordered j i (by omega) hi
    exact ⟨k,Ne.symm hk⟩

/-- Periodic high-only block words cannot contain both F-F and exceptional-F. -/
theorem periodic_word_constant (A R : Nat → Int) (e : Nat → Bool)
    (hper : ∃ l,IsPeriod e l) (hodd : ∀ n,R n%2=1)
    (hA : LinearBound A)
    (hs : ∀ n,A (n+1)=4*A n-(if e n then 2*R n else 0)+blockConstant (e n) (R n))
    (hR : ∀ n,R (n+1)=R n+delta (e n) (R n)) :
    (∀ n,e n=false) ∨ (∀ n,e n=true) := by
  by_cases hfalse : ∀ n,e n=false
  · exact Or.inl hfalse
  by_cases htrue : ∀ n,e n=true
  · exact Or.inr htrue
  exfalso
  have hlo : ∃ n,e n=false := by
    by_cases h : ∃ n,e n=false
    · exact h
    · apply False.elim
      apply htrue
      intro n; cases hh : e n
      · exact False.elim (h ⟨n,hh⟩)
      · rfl
  have hhi : ∃ n,e n=true := by
    by_cases h : ∃ n,e n=true
    · exact h
    · apply False.elim
      apply hfalse
      intro n; cases hh : e n
      · rfl
      · exact False.elim (h ⟨n,hh⟩)
  obtain ⟨l,hl⟩ := hper
  obtain ⟨m,hm,hmin⟩ := least_period e l hl
  have hlo' : ∃ n<m,e n=false := by
    obtain ⟨n,hn⟩ := hlo
    exact ⟨n%m,Nat.mod_lt n hm.1,by rw [← period_reduce e m hm n,hn]⟩
  have hhi' : ∃ n<m,e n=true := by
    obtain ⟨n,hn⟩ := hhi
    exact ⟨n%m,Nat.mod_lt n hm.1,by rw [← period_reduce e m hm n,hn]⟩
  have hlarge : 2≤m := by
    obtain ⟨i,hi,hif⟩ := hlo'
    obtain ⟨j,hj,hjt⟩ := hhi'
    by_cases heq : i=j
    · rw [heq,hjt] at hif; contradiction
    · omega
  exact forward_no_mixed A R e m hlarge hodd hm.2 hlo' hhi'
    (least_period_primitive e m hm hmin) hA hs hR

theorem linear_scale {f : Nat → Int} (h : LinearBound f) (a : Int) :
    LinearBound (fun n => a*f n) := by
  obtain ⟨B,G,hb⟩ := h
  refine ⟨a.natAbs*B,a.natAbs*G,?_⟩
  intro n
  have hh := Nat.mul_le_mul_left a.natAbs (hb n)
  rw [Nat.mul_add,← Nat.mul_assoc] at hh
  dsimp only
  rw [Int.natAbs_mul]
  exact hh

theorem linear_index_scale {f : Nat → Int} (h : LinearBound f) (s : Nat) :
    LinearBound (fun n => f (s*n)) := by
  obtain ⟨B,G,hb⟩ := h
  refine ⟨B,G*s,?_⟩
  intro n
  have hh := hb (s*n)
  rw [← Nat.mul_assoc] at hh
  exact hh

theorem rank_linear (R : Nat → Int) (e : Nat → Bool)
    (hR : ∀ n,R (n+1)=R n+delta (e n) (R n)) : LinearBound R := by
  refine ⟨(R 0).natAbs,14,?_⟩
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hd := delta_bounds (e n) (R n)
    have ha := Int.natAbs_add_le (R n) (delta (e n) (R n))
    have habs := Int.natAbs_of_nonneg (show 0≤delta (e n) (R n) by omega)
    rw [hR]
    omega

/-- All-exceptional blocks force the exact two affine rays, at every phase. -/
theorem exceptional_corridor (A R : Nat → Int) (e : Nat → Bool)
    (hodd : ∀ n,R n%2=1) (hA : LinearBound A) (hall : ∀ n,e n=true)
    (hs : ∀ n,A (n+1)=4*A n-(if e n then 2*R n else 0)+blockConstant (e n) (R n))
    (hR : ∀ n,R (n+1)=R n+delta (e n) (R n)) :
    ∀ n,(R n%4=3 ∧ 3*A n-2*R n=2) ∨ (R n%4=1 ∧ 3*A n-2*R n= -6) := by
  let D := fun n => 3*A n-2*R n
  have hDb : LinearBound D := linear_sub (linear_scale hA 3) (linear_scale (rank_linear R e hR) 2)
  have hD : ∀ n,D (n+1)=4*D n+(if R n%4=1 then 26 else -14) := by
    intro n
    have ha := hs n
    have hr := hR n
    rw [hall] at ha hr
    simp [blockConstant,delta] at ha hr
    dsimp [D]
    by_cases h : R n%4=1 <;> simp [h] at ha hr ⊢ <;> omega
  have hD2 : ∀ n,D (n+2)=16*D n+(if R n%4=1 then 90 else -30) := by
    intro n
    have h1 := hD n
    have h2 := hD (n+1)
    rw [show n+1+1=n+2 by omega] at h2
    have hmod := rank_mod4 R e hR n 1
    have ho := hodd n
    by_cases h : R n%4=1
    · have hn : R (n+1)%4≠1 := by omega
      simp [h,hn] at h1 h2 ⊢
      omega
    · have hn : R (n+1)%4=1 := by omega
      simp [h,hn] at h1 h2 ⊢
      omega
  intro n
  let X := fun k => D (2*k+n)
  have hbX : LinearBound X := linear_index_scale (linear_shift hDb n) 2
  obtain ⟨B,G,hb⟩ := hbX
  have hX : ∀ k,X (k+1)=16*X k+(if R n%4=1 then 90 else -30) := by
    intro k
    have hmod := rank_mod4 R e hR n (2*k)
    have hmod' : R (2*k+n)%4=R n%4 := by rw [Nat.add_comm]; omega
    dsimp [X]
    rw [show 2*(k+1)+n=2*k+n+2 by omega,hD2,hmod']
  by_cases h : R n%4=1
  · right
    refine ⟨h,?_⟩
    have hx : ∀ k,X (k+1)=16*X k-(-90) := by intro k; have hh:=hX k; simp [h] at hh; omega
    have hh := affine_rigidity 16 (-90) X (by decide) hx B G hb
    simp [X,D] at hh
    omega
  · left
    have ho := hodd n
    refine ⟨by omega,?_⟩
    have hx : ∀ k,X (k+1)=16*X k-30 := by intro k; have hh:=hX k; simp [h] at hh; omega
    have hh := affine_rigidity 16 30 X (by decide) hx B G hb
    simp [X,D] at hh
    omega

/-- Full classification for periodic high-only block words in the natural
    source map: the all-first option is impossible, and both remaining
    odd-rank phases lie on the known four-step escape corridor. -/
theorem periodic_block_corridor (A R : Nat → Int) (e : Nat → Bool)
    (hper : ∃ l,IsPeriod e l) (hodd : ∀ n,R n%2=1)
    (hA : LinearBound A) (hpos : 0<A 0)
    (hs : ∀ n,A (n+1)=4*A n-(if e n then 2*R n else 0)+blockConstant (e n) (R n))
    (hR : ∀ n,R (n+1)=R n+delta (e n) (R n)) :
    (∀ n,e n=true) ∧
    (∀ n,(R n%4=3 ∧ 3*A n-2*R n=2) ∨ (R n%4=1 ∧ 3*A n-2*R n= -6)) := by
  rcases periodic_word_constant A R e hper hodd hA hs hR with hfalse|htrue
  · exfalso
    have hrec : ∀ n,A (n+1)=4*A n := by
      intro n; have hh:=hs n; simpa [hfalse,blockConstant] using hh
    have hzero := linear_geometric_zero hA hrec 0
    omega
  · exact ⟨htrue,exceptional_corridor A R e hodd hA htrue hs hR⟩

#print axioms least_period_primitive
#print axioms periodic_word_constant
#print axioms exceptional_corridor
#print axioms periodic_block_corridor

end BB429.PeriodicHigh
