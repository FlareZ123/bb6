import BB429PeriodicClassification

namespace BB429.PeriodicHigh

private theorem reduce_period {α : Type} (f : Nat → α) (l : Nat)
    (h : ∀ n, f (n+l)=f n) (n : Nat) : f n=f (n%l) := by
  have hh : ∀ a k, f (a+l*k)=f a := by
    intro a k
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.mul_succ,← Nat.add_assoc,h,ih]
  conv => lhs; rw [← Nat.mod_add_div n l]
  exact hh _ _

def revIndex (l n : Nat) : Nat := l-1-n%l

theorem revIndex_period (l n : Nat) : revIndex l (n+l)=revIndex l n := by
  simp [revIndex,Nat.add_mod_right]

theorem revIndex_lt {l : Nat} (hl : 0<l) (n : Nat) : revIndex l n<l := by
  unfold revIndex; omega

theorem revIndex_involutive {l : Nat} (hl : 0<l) (n : Nat) : revIndex l (revIndex l n)=n%l := by
  have hh := Nat.mod_lt n hl
  have hi := revIndex_lt hl n
  unfold revIndex at *
  rw [Nat.mod_eq_of_lt hi]
  omega

theorem highCount_reverse (e : Nat → Bool) (l : Nat) :
    highCount (fun n => e (revIndex l n)) l = highCount e l := by
  have hl : (List.range l).map (revIndex l)=(List.range l).reverse := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      have hi' : i<l := by simpa using hi
      simp [revIndex,List.getElem_reverse,Nat.mod_eq_of_lt hi']
  unfold highCount
  have hh := congrArg (fun xs : List Nat => (xs.filter e).length) hl
  rw [List.filter_map,List.length_map,List.filter_reverse,List.length_reverse] at hh
  exact hh

/-- Reversing the primitive cycle changes neither its length nor digit counts. -/
theorem reverse_no_mixed_cycle (p : Nat → Int) (e : Nat → Bool) (m l : Nat)
    (hm : 0<m) (hl : 2≤l) (hp : ∀ n, p (n+l)=p n)
    (he : ∀ n, e (n+l)=e n)
    (hlo : ∃ n<l, e n=false) (hhi : ∃ n<l, e n=true)
    (hprim : ∀ i j, i<l → j<l → i≠j → ∃ k, e (i+k)≠e (j+k))
    (hs : ∀ n, p n=4*p (n+1)-(if e n then 2*(m:Int) else 0))
    (hEven : l%2=0 → 2*m≤7*l)
    (hOdd : l%2=1 → m≤3*(l+highCount e l)) : False := by
  let q := fun n => p (l-n%l)
  let f := fun n => e (revIndex l n)
  have hq : ∀ n,q (n+l)=q n := by intro n; simp [q,Nat.add_mod_right]
  have hf : ∀ n,f (n+l)=f n := by intro n; simp [f,revIndex_period]
  have hrec : ∀ n,q (n+1)=4*q n-(if f n then 2*(m:Int) else 0) := by
    intro n
    have hmod := Nat.mod_lt n (show 0<l by omega)
    have hmod' := Nat.mod_lt (n+1) (show 0<l by omega)
    have hh := hs (revIndex l n)
    have h1 : revIndex l n+1=l-n%l := by unfold revIndex; omega
    rw [h1] at hh
    have h2 : (n+1)%l=(n%l+1)%l := by rw [Nat.mod_add_mod]
    dsimp [q,f]
    rw [h2]
    by_cases h : n%l+1<l
    · rw [Nat.mod_eq_of_lt h]
      have h3 : l-(n%l+1)=revIndex l n := by unfold revIndex; omega
      rw [h3]
      exact hh
    · have h3 : n%l+1=l := by omega
      rw [h3,Nat.mod_self,Nat.sub_zero]
      have hp0 : p l=p 0 := by simpa using hp 0
      rw [hp0]
      have h4 : revIndex l n=0 := by unfold revIndex; omega
      conv at hh => lhs; rw [h4]
      exact hh
  have hocc : ∀ b : Bool, (∃ i<l,e i=b) → ∃ i<l,f i=b := by
    intro b h
    obtain ⟨i,hi,hei⟩ := h
    refine ⟨revIndex l i,revIndex_lt (by omega) i,?_⟩
    dsimp [f]
    rw [revIndex_involutive (by omega),Nat.mod_eq_of_lt hi,hei]
  have hprim' : ∀ i j,i<l → j<l → i≠j → ∃ k,f (i+k)≠f (j+k) := by
    intro i j hi hj hij
    by_cases hn : ∃ k,f (i+k)≠f (j+k)
    · exact hn
    exfalso
    have hh : ∀ k,f (i+k)=f (j+k) := by
      intro k
      by_cases h : f (i+k)=f (j+k)
      · exact h
      · exact False.elim (hn ⟨k,h⟩)
    let a := revIndex l i
    let b := revIndex l j
    have ha : a<l := revIndex_lt (by omega) i
    have hb : b<l := revIndex_lt (by omega) j
    have hab : a≠b := by
      intro h
      dsimp [a,b,revIndex] at h
      rw [Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj] at h
      omega
    obtain ⟨k,hk⟩ := hprim a b ha hb hab
    let t := k%l
    have ht : t<l := Nat.mod_lt _ (by omega)
    have hsum : ∀ x, x<l → revIndex l (x+(l-t))=(revIndex l x+t)%l := by
      intro x hx
      unfold revIndex
      rw [Nat.mod_eq_of_lt hx]
      by_cases h : t≤x
      · have h1 : x+(l-t)=x-t+l := by omega
        rw [h1,Nat.add_mod_right,Nat.mod_eq_of_lt (show x-t<l by omega),Nat.mod_eq_of_lt (show l-1-x+t<l by omega)]
        omega
      · rw [Nat.mod_eq_of_lt (show x+(l-t)<l by omega)]
        have h1 : l-1-x+t=(t-x-1)+l := by omega
        rw [h1,Nat.add_mod_right,Nat.mod_eq_of_lt (show t-x-1<l by omega)]
        omega
    have hh' := hh (l-t)
    dsimp [f] at hh'
    rw [hsum i hi,hsum j hj] at hh'
    change e ((a+t)%l)=e ((b+t)%l) at hh'
    apply hk
    rw [reduce_period e l he (a+k),reduce_period e l he (b+k)]
    have h1 : (a+k)%l=(a+t)%l := by dsimp [t]; rw [Nat.add_mod a k l,Nat.add_mod a (k%l) l,Nat.mod_mod]
    have h2 : (b+k)%l=(b+t)%l := by dsimp [t]; rw [Nat.add_mod b k l,Nat.add_mod b (k%l) l,Nat.mod_mod]
    rwa [h1,h2]
  exact no_mixed_cycle q f m l hm hl hq hf (hocc false hlo) (hocc true hhi) hprim' hrec hEven (by intro h; rw [highCount_reverse]; exact hOdd h)

/-- Negating the backwards rank puts its drift into the forward form. -/
theorem reverse_rank_drift (R : Nat → Int) (e : Nat → Bool)
    (hodd : ∀ n,R n%2=1)
    (hR : ∀ n,R n=R (n+1)+delta (e n) (R (n+1))) :
    ∀ n,-R (n+1) = -R n+delta (e n) (-R n) := by
  intro n
  have hh := hR n
  have hd := (delta_bounds (e n) (R (n+1))).2.2
  have ho := hodd n
  have hmod : (-R n)%4=R (n+1)%4 := by omega
  have heq : delta (e n) (-R n)=delta (e n) (R (n+1)) := by simp [delta,hmod]
  omega

theorem backward_no_mixed (A R : Nat → Int) (e : Nat → Bool) (l : Nat)
    (hl : 2≤l) (hodd : ∀ n,R n%2=1)
    (he : ∀ n,e (n+l)=e n)
    (hlo : ∃ n<l,e n=false) (hhi : ∃ n<l,e n=true)
    (hprim : ∀ i j,i<l → j<l → i≠j → ∃ k,e (i+k)≠e (j+k))
    (hs : ∀ n,A n=4*A (n+1)-(if e n then 2*R (n+1) else 0)+blockConstant (e n) (R (n+1)))
    (hR : ∀ n,R n=R (n+1)+delta (e n) (R (n+1))) : False := by
  let L := if l%2=0 then l else 2*l
  let S := fun n => -R n
  have hS : ∀ n,S (n+1)=S n+delta (e n) (S n) := reverse_rank_drift R e hodd hR
  have hodd' : ∀ n,S n%2=1 := by intro n; dsimp [S]; have hh:=hodd n; omega
  obtain ⟨m,hm,hL,hdrift,hc,hEven,hOdd⟩ := period_drift S e l (by omega) hodd' he hS
  change (∀ n,e (n+L)=e n) at hL
  change (∀ n,S (n+L)=S n+4*(m:Int)) at hdrift
  have hRd : ∀ n,R (n+L)=R n-4*(m:Int) := by
    intro n; have hh:=hdrift n; dsimp [S] at hh; omega
  have hc' : ∀ n,blockConstant (e (n+L)) (R (n+L+1))=blockConstant (e n) (R (n+1)) := by
    intro n
    have hh:=hRd (n+1)
    rw [show n+1+L=n+L+1 by omega] at hh
    have hmod : R (n+L+1)%4=R (n+1)%4 := by omega
    simp [blockConstant,hL,hmod]
  obtain ⟨p,hp,hrec⟩ := periodic_difference_backward A R e (fun n=>blockConstant (e n) (R (n+1))) L l m hs hRd hL hc' he
  exact reverse_no_mixed_cycle p e m l hm hl hp he hlo hhi hprim hrec hEven hOdd

theorem backward_periodic_constant (A R : Nat → Int) (e : Nat → Bool)
    (hper : ∃ l,IsPeriod e l) (hodd : ∀ n,R n%2=1)
    (hs : ∀ n,A n=4*A (n+1)-(if e n then 2*R (n+1) else 0)+blockConstant (e n) (R (n+1)))
    (hR : ∀ n,R n=R (n+1)+delta (e n) (R (n+1))) :
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
  exact backward_no_mixed A R e m hlarge hodd hm.2 hlo' hhi'
    (least_period_primitive e m hm hmin) hs hR

/-- An infinite integral reversed all-exceptional block trajectory lies on
    the same two corridor phases, with no linear bound assumption. -/
theorem backward_exceptional_corridor (A R : Nat → Int) (e : Nat → Bool)
    (hodd : ∀ n,R n%2=1) (hall : ∀ n,e n=true)
    (hs : ∀ n,A n=4*A (n+1)-(if e n then 2*R (n+1) else 0)+blockConstant (e n) (R (n+1)))
    (hR : ∀ n,R n=R (n+1)+delta (e n) (R (n+1))) :
    ∀ n,(R n%4=3 ∧ 3*A n-2*R n=2) ∨ (R n%4=1 ∧ 3*A n-2*R n= -6) := by
  let D := fun n => 3*A n-2*R n
  have hflip : ∀ n,R n%4=(R (n+1)+2)%4 := by
    intro n; have hh:=hR n; have hd:=(delta_bounds (e n) (R (n+1))).2.2; omega
  have hD : ∀ n,D n=4*D (n+1)+(if R (n+1)%4=1 then 26 else -14) := by
    intro n
    have ha:=hs n
    have hr:=hR n
    rw [hall] at ha hr
    simp [blockConstant,delta] at ha hr
    dsimp [D]
    by_cases h : R (n+1)%4=1 <;> simp [h] at ha hr ⊢ <;> omega
  have hD2 : ∀ n,D n=16*D (n+2)+(if R n%4=1 then 90 else -30) := by
    intro n
    have h1:=hD n
    have h2:=hD (n+1)
    have h3:=hflip n
    have h4:=hflip (n+1)
    have ho:=hodd n
    rw [show n+1+1=n+2 by omega] at h2 h4
    by_cases h : R n%4=1
    · have hn : R (n+1)%4≠1 := by omega
      have hn2 : R (n+2)%4=1 := by omega
      simp [h,hn,hn2] at h1 h2 ⊢
      omega
    · have hn : R (n+1)%4=1 := by omega
      have hn2 : R (n+2)%4≠1 := by omega
      simp [h,hn,hn2] at h1 h2 ⊢
      omega
  have hp : ∀ n k,R (n+2*k)%4=R n%4 := by
    intro n k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1:=hflip (n+2*k)
      have h2:=hflip (n+2*k+1)
      rw [show n+2*(k+1)=n+2*k+1+1 by omega]
      omega
  intro n
  by_cases h : R n%4=1
  · right
    refine ⟨h,?_⟩
    let X := fun k => D (n+2*k)+6
    have hX : ∀ k,X k=16*X (k+1) := by
      intro k; dsimp [X]; have hh:=hD2 (n+2*k); rw [hp,h] at hh; simp at hh
      rw [show n+2*(k+1)=n+2*k+2 by omega]; omega
    have hh:=reverse_geometric_zero 16 X (by decide) hX
    simp [X,D] at hh
    omega
  · left
    refine ⟨by have hh:=hodd n; omega,?_⟩
    let X := fun k => D (n+2*k)-2
    have hX : ∀ k,X k=16*X (k+1) := by
      intro k; dsimp [X]; have hh:=hD2 (n+2*k); rw [hp] at hh; simp [h] at hh
      rw [show n+2*(k+1)=n+2*k+2 by omega]; omega
    have hh:=reverse_geometric_zero 16 X (by decide) hX
    simp [X,D] at hh
    omega

theorem backward_periodic_corridor (A R : Nat → Int) (e : Nat → Bool)
    (hper : ∃ l,IsPeriod e l) (hodd : ∀ n,R n%2=1) (hne : A 0≠0)
    (hs : ∀ n,A n=4*A (n+1)-(if e n then 2*R (n+1) else 0)+blockConstant (e n) (R (n+1)))
    (hR : ∀ n,R n=R (n+1)+delta (e n) (R (n+1))) :
    (∀ n,e n=true) ∧ ∀ n,(R n%4=3 ∧ 3*A n-2*R n=2) ∨ (R n%4=1 ∧ 3*A n-2*R n= -6) := by
  rcases backward_periodic_constant A R e hper hodd hs hR with hfalse|htrue
  · exfalso
    apply hne
    apply reverse_geometric_zero 4 A (by decide)
    intro n; have hh:=hs n; simpa [hfalse,blockConstant] using hh
  · exact ⟨htrue,backward_exceptional_corridor A R e hodd htrue hs hR⟩

#print axioms reverse_no_mixed_cycle
#print axioms backward_periodic_corridor

end BB429.PeriodicHigh
