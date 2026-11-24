import BB429PeriodicHigh

namespace BB429.PeriodicHigh

def highCount (e : Nat → Bool) (l : Nat) : Nat := ((List.range l).filter e).length

/-- A cyclic sequence cannot be negative anywhere if every next value is
    at most four times its predecessor. -/
theorem cyclic_nonnegative (p : Nat → Int) (l : Nat) (hl : 0<l)
    (hp : ∀ n, p (n+l)=p n) (hs : ∀ n, p (n+1)≤4*p n) : ∀ n, 0≤p n := by
  intro n
  by_cases h : 0≤p n
  · exact h
  exfalso
  have hneg : ∀ j, p (n+j+1)<p n := by
    intro j
    induction j with
    | zero => have hh := hs n; simp; omega
    | succ j ih =>
      have hh := hs (n+j+1)
      rw [show n+(j+1)+1=n+j+1+1 by omega]
      omega
  have hj := hneg (l-1)
  rw [show n+(l-1)+1=n+l by omega, hp] at hj
  omega

/-- If a negative drift occurs again in the future, zero is impossible too. -/
theorem cyclic_positive (p : Nat → Int) (l : Nat) (hl : 0<l)
    (hp : ∀ n, p (n+l)=p n) (hs : ∀ n, p (n+1)≤4*p n)
    (hf : ∀ n, ∃ j, p (n+j+1)<4*p (n+j)) : ∀ n, 0<p n := by
  have hnn := cyclic_nonnegative p l hl hp hs
  intro n
  by_cases h : 0<p n
  · exact h
  exfalso
  have hn := hnn n
  have hz : ∀ j, p (n+j)=0 := by
    intro j
    induction j with
    | zero => simp; omega
    | succ j ih =>
      have hh := hs (n+j)
      have hn' := hnn (n+j+1)
      rw [show n+(j+1)=n+j+1 by omega]
      omega
  obtain ⟨j,hj⟩ := hf n
  have hz' := hz (j+1)
  rw [show n+(j+1)=n+j+1 by omega] at hz'
  have hh := hz j
  omega

/-- Every digit occurring in a periodic word occurs again after any index. -/
theorem periodic_occurs (e : Nat → Bool) (l : Nat) (hl : 0<l)
    (he : ∀ n, e (n+l)=e n) (b : Bool) (hex : ∃ j, e j=b) :
    ∀ n, ∃ j, e (n+j)=b := by
  obtain ⟨j,hj⟩ := hex
  intro n
  have hmul : ∀ k, e (j+l*k)=e j := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.mul_succ, ← Nat.add_assoc, he, ih]
  have hle : n≤j+l*n := by
    have hh := Nat.mul_le_mul_right n (show 1≤l by omega)
    simp at hh
    omega
  refine ⟨j+l*n-n, ?_⟩
  rw [show n+(j+l*n-n)=j+l*n by omega, hmul, hj]

/-- The two digit intervals are strict for a genuinely mixed periodic word. -/
theorem mixed_cycle_intervals (p : Nat → Int) (e : Nat → Bool) (m l : Nat)
    (hm : 0<m) (hl : 0<l) (hp : ∀ n, p (n+l)=p n)
    (he : ∀ n, e (n+l)=e n)
    (hlo : ∃ n, e n=false) (hhi : ∃ n, e n=true)
    (hs : ∀ n, p (n+1)=4*p n-(if e n then 2*(m:Int) else 0)) :
    (∀ n, 0<p n ∧ 3*p n<2*(m:Int) ∧ p n%2=0) ∧
    (∀ n, if e n then HighDigit m (p n).toNat else Low m (p n).toNat) := by
  have hpos : ∀ n, 0<p n := by
    apply cyclic_positive p l hl hp
    · intro n; have hh := hs n; cases h : e n <;> simp [h] at hh <;> omega
    · intro n
      obtain ⟨j,hj⟩ := periodic_occurs e l hl he true hhi n
      refine ⟨j, ?_⟩
      have hh := hs (n+j)
      simp [hj] at hh
      omega
  let q := fun n => 2*(m:Int)-3*p n
  have hq : ∀ n, 0<q n := by
    apply cyclic_positive q l hl
    · intro n; dsimp [q]; rw [hp]
    · intro n
      dsimp [q]
      have hh := hs n
      cases h : e n <;> simp [h] at hh <;> omega
    · intro n
      obtain ⟨j,hj⟩ := periodic_occurs e l hl he false hlo n
      refine ⟨j, ?_⟩
      dsimp [q]
      have hh := hs (n+j)
      simp [hj] at hh
      omega
  have heven : ∀ n, p n%2=0 := by
    intro n
    have hh := hs (n+l-1)
    rw [show n+l-1+1=n+l by omega,hp] at hh
    cases h : e (n+l-1) <;> simp [h] at hh <;> omega
  constructor
  · intro n
    have hh := hq n
    dsimp [q] at hh
    exact ⟨hpos n,by omega,heven n⟩
  · intro n
    have hh := hq n
    have hn := hq (n+1)
    dsimp [q] at hh hn
    have h1 := hpos n
    have h2 := hpos (n+1)
    have hp' := heven n
    have hr := hs n
    have ht := Int.toNat_of_nonneg (show 0≤p n by omega)
    cases h : e n <;> simp [h,Low,HighDigit] at hr ⊢ <;> omega

/-- Equality of two cyclic numerators forces identical infinite digit tails. -/
theorem equal_numerator_same_tail (p : Nat → Int) (e : Nat → Bool) (m : Nat)
    (_hm : 0<m) (hb : ∀ n, 0<p n ∧ 3*p n<2*(m:Int))
    (hs : ∀ n, p (n+1)=4*p n-(if e n then 2*(m:Int) else 0))
    (i j : Nat) (h : p i=p j) : ∀ k, e (i+k)=e (j+k) := by
  have heq : ∀ k, p (i+k)=p (j+k) ∧ e (i+k)=e (j+k) := by
    have hdet : ∀ a b, p a=p b → e a=e b := by
      intro a b hh
      have ha := hs a
      have hb' := hs b
      obtain ⟨h1,h2⟩ := hb (a+1)
      obtain ⟨h3,h4⟩ := hb (b+1)
      cases ea : e a <;> cases eb : e b <;> simp [ea,eb] at ha hb' ⊢ <;> omega
    intro k
    induction k with
    | zero => simpa using And.intro h (hdet i j h)
    | succ k ih =>
      have ha := hs (i+k)
      have hb' := hs (j+k)
      rw [ih.1,ih.2] at ha
      have hh : p (i+(k+1))=p (j+(k+1)) := by
        rw [show i+(k+1)=i+k+1 by omega,show j+(k+1)=j+k+1 by omega]
        omega
      exact ⟨hh,hdet _ _ hh⟩
  exact fun k => (heq k).2

/-- The full integral mixed-cycle contradiction. The primitive assumption
    states that no two positions within the period have equal infinite tails.
    The two drift bounds come from the alternating rank residues. -/
theorem no_mixed_cycle (p : Nat → Int) (e : Nat → Bool) (m l : Nat)
    (hm : 0<m) (hl : 2≤l) (hp : ∀ n, p (n+l)=p n)
    (he : ∀ n, e (n+l)=e n)
    (hlo : ∃ n<l, e n=false) (hhi : ∃ n<l, e n=true)
    (hprim : ∀ i j, i<l → j<l → i≠j → ∃ k, e (i+k)≠e (j+k))
    (hs : ∀ n, p (n+1)=4*p n-(if e n then 2*(m:Int) else 0))
    (hEven : l%2=0 → 2*m≤7*l)
    (hOdd : l%2=1 → m≤3*(l+highCount e l)) : False := by
  have hinterval := mixed_cycle_intervals p e m l hm (by omega) hp he
    (by obtain ⟨n,_,hn⟩ := hlo; exact ⟨n,hn⟩)
    (by obtain ⟨n,_,hn⟩ := hhi; exact ⟨n,hn⟩) hs
  have hdiff : ∀ i j, i<l → j<l → i≠j → (p i).toNat≠(p j).toNat := by
    intro i j hi hj hij hh
    have hpi := Int.toNat_of_nonneg (show 0≤p i by have h:=hinterval.1 i; omega)
    have hpj := Int.toNat_of_nonneg (show 0≤p j by have h:=hinterval.1 j; omega)
    have hsame := equal_numerator_same_tail p e m hm
      (fun n => ⟨(hinterval.1 n).1,(hinterval.1 n).2.1⟩) hs i j (by omega)
    obtain ⟨k,hk⟩ := hprim i j hi hj hij
    exact hk (hsame k)
  let ps := (List.range l).map (fun i => (p i).toNat)
  let qs := ((List.range l).filter e).map (fun i => (p i).toNat)
  have hnd : ps.Nodup := by
    unfold ps
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    apply List.Pairwise.imp_of_mem _ (List.nodup_iff_pairwise_ne.mp List.nodup_range)
    intro i j hi hj hij
    exact hdiff i j (List.mem_range.mp hi) (List.mem_range.mp hj) hij
  have hndq : qs.Nodup := by
    unfold qs
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    have hn : ((List.range l).filter e).Nodup := List.Nodup.sublist List.filter_sublist List.nodup_range
    apply List.Pairwise.imp_of_mem _ (List.nodup_iff_pairwise_ne.mp hn)
    intro i j hi hj hij
    exact hdiff i j (List.mem_range.mp (List.mem_filter.mp hi).1) (List.mem_range.mp (List.mem_filter.mp hj).1) hij
  have hps : ∀ v∈ps, Low m v ∨ HighDigit m v := by
    intro v hv
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hv
    have hh := hinterval.2 i
    cases h : e i <;> simp [h] at hh
    · exact Or.inl hh
    · exact Or.inr hh
  have hqs : ∀ v∈qs, HighDigit m v := by
    intro v hv
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hv
    have hh := hinterval.2 i
    have he' := (List.mem_filter.mp hi).2
    simpa [he'] using hh
  have hc := mixed_count hm ps hnd hps
  have hcount := high_count hm qs hndq hqs
  have hsubset : qs ⊆ highList m := fun v hv => high_mem (hqs v hv)
  have hexact := hndq.length_le_of_subset hsubset
  simp [ps] at hc
  simp [qs] at hcount hexact
  change 12*highCount e l < m+12 at hcount
  change highCount e l ≤ (highList m).length at hexact
  have hlt : highCount e l < l := by
    have hh := List.length_filter_le e (List.range l)
    simp at hh
    by_cases h : ((List.range l).filter e).length=l
    · obtain ⟨i,hi,hfalse⟩ := hlo
      have hall := (List.length_filter_eq_length_iff (p:=e) (l:=List.range l)).mp (by simpa only [List.length_range] using h)
      have ht := hall i (List.mem_range.mpr hi)
      simp [hfalse] at ht
    · unfold highCount; omega
  by_cases hpar : l%2=0
  · have hb := hEven hpar
    have hsmall : l=2 ∧ m=7 := by omega
    obtain ⟨i,hi,hfalse⟩ := hlo
    have hh := hinterval.2 i
    simp [hfalse,Low] at hh
    omega
  · have hb := hOdd (by omega)
    have hsmall : l=3 ∧ highCount e l=2 ∧ 13≤m ∧ m≤15 := by omega
    simp [highList] at hexact
    omega

#print axioms mixed_cycle_intervals
#print axioms equal_numerator_same_tail
#print axioms no_mixed_cycle

end BB429.PeriodicHigh
