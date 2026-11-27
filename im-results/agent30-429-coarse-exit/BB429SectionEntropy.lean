import BB429Resonance

namespace BB429.CoarseExit

private theorem filter_split_len (l : List Nat) (p : Nat → Bool) :
    (l.filter p).length+(l.filter fun a=> !p a).length=l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : p a <;> simp [List.filter_cons,h] <;> omega

/-- Binary signatures with bounded fibers. No finite enumeration of a word
    tree is required for the cardinality bound. -/
theorem binary_fiber_bound (n M : Nat) (l : List Nat) (e : Nat → Nat → Bool)
    (hn : l.Nodup)
    (h : ∀ xs : List Nat, xs ⊆ l → xs.Nodup →
      (∀ x∈xs, ∀ y∈xs, ∀ i, i<n → e x i=e y i) → xs.length≤M) :
    l.length≤2^n*M := by
  induction n generalizing l with
  | zero => simpa using h l (by intro x hx; exact hx) hn (by omega)
  | succ n ih =>
    let a := l.filter (fun x=>e x n)
    let b := l.filter (fun x=> !e x n)
    have ha : a.length≤2^n*M := by
      apply ih a (List.filter_sublist.nodup hn)
      intro xs hxs hnd hs
      apply h xs (by intro x hx; exact (List.mem_filter.mp (hxs hx)).1) hnd
      intro x hx y hy i hi
      by_cases hk : i<n
      · exact hs x hx y hy i hk
      · have he : i=n := by omega
        subst i
        exact (List.mem_filter.mp (hxs hx)).2.trans (List.mem_filter.mp (hxs hy)).2.symm
    have hb : b.length≤2^n*M := by
      apply ih b (List.filter_sublist.nodup hn)
      intro xs hxs hnd hs
      apply h xs (by intro x hx; exact (List.mem_filter.mp (hxs hx)).1) hnd
      intro x hx y hy i hi
      by_cases hk : i<n
      · exact hs x hx y hy i hk
      · have he : i=n := by omega
        subst i
        have hx' := (List.mem_filter.mp (hxs hx)).2
        have hy' := (List.mem_filter.mp (hxs hy)).2
        simp at hx' hy'
        exact hx'.trans hy'.symm
    have hl : a.length+b.length=l.length := filter_split_len l (fun x=>e x n)
    rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 2 M, ←Nat.mul_assoc, Nat.mul_comm _ 2]
    omega

/-- List of distinct integers in an interval of diameter at most D. -/
theorem diameter_bound (l : List Nat) (D : Nat) (hn : l.Nodup)
    (h : ∀ x∈l, ∀ y∈l, x≤y → y-x≤D) : l.length≤D+1 := by
  cases he : l.min? with
  | none => have hnil := List.min?_eq_none_iff.mp he; simp [hnil]
  | some a =>
    have hmin := List.min?_eq_some_iff.mp he
    have hs : l ⊆ List.range' a (D+1) := by
      intro x hx
      have hax := hmin.2 x hx
      have hD := h a hmin.1 x hx hax
      apply List.mem_range'.mpr
      exact ⟨x-a,by omega,by omega⟩
    simpa using hn.length_le_of_subset hs

/-- For identical ordinary words the rank difference is constant and the
    first-coordinate difference is minus twice the base-four word times it. -/
theorem phase_word_difference (U V U' V' : Nat → Int) (e f ph ph' : Nat → Bool) (n : Nat)
    (hU : U 0=U' 0) (hph : ph 0=ph' 0) (hs : PhaseBlocks U V e ph n) (hs' : PhaseBlocks U' V' f ph' n)
    (he : ∀ i, i<n → e i=f i) : ∀ i, i≤n → ph i=ph' i ∧ V' i-V i=V' 0-V 0 ∧
      U i-U' i=2*word4 e i*(V' 0-V 0) := by
  intro i hi
  induction i with
  | zero => simp [word4,hU,hph]
  | succ i ih =>
    obtain ⟨hp,hv,hu⟩ := ih (by omega)
    obtain ⟨hpi,hui,hvi⟩ := hs i (by omega)
    obtain ⟨hpi',hui',hvi'⟩ := hs' i (by omega)
    rw [←hp] at hpi'
    rw [←he i (by omega),←hp] at hui' hvi'
    refine ⟨by rw [hpi,hpi'],by rw [hvi,hvi']; omega,?_⟩
    rw [hui,hui',word4]
    cases h : e i <;> cases hq : ph i <;> simp [h,hq] at * <;> grind +ring

 theorem word4_first_bound (e : Nat → Bool) (k : Nat) (h : e 0=true) :
    (4:Int)^k≤word4 e (k+1) := by
  induction k with
  | zero => simp [word4,h]
  | succ k ih =>
    rw [Int.pow_succ,word4]
    cases e (k+1) <;> simp <;> omega

 theorem phase_rank_bound (U V : Nat → Int) (e ph : Nat → Bool) (n : Nat)
    (hs : PhaseBlocks U V e ph n) : ∀ i, i≤n → V i≤V 0+42*i := by
  intro i hi
  induction i with
  | zero => simp
  | succ i ih =>
    have h := ih (by omega)
    obtain ⟨_,_,hv⟩ := hs i (by omega)
    cases e i <;> cases ph i <;> simp_all <;> omega

 theorem first_digit (u w : Nat) (U V : Nat → Int) (e ph : Nat → Bool) (n : Nat)
    (hn : 0<n) (hW : w<2*u+3) (hU : U 0=Uc (u,w)) (hV : V 0=Vc (u,w))
    (hs : PhaseBlocks U V e ph n) (hp : Physical U V n) : e 0=true := by
  by_cases h : e 0=true
  · exact h
  · have hf : e 0=false := Bool.eq_false_iff.mpr h
    obtain ⟨_,hu,hv⟩ := hs 0 hn
    have hh := hp 1 (by omega)
    simp [hf,hU,hV,Uc,Vc] at hu hv
    omega

/-- A long excursion and its source-verified branch signature. -/
def longExcursion (p : State) (n : Nat) : Prop := good p (2*n) ∧ avoid p (2*n)

noncomputable def sourceWord (p : State) (n : Nat) : Nat → Bool := by
  classical
  exact if h : p.2%2=1 ∧ longExcursion p n then
    Classical.choose (tracePhasePrefix p n (2*n) h.1 h.2.1 h.2.2 (by omega)).2
  else fun _=>false

 theorem sourceWord_sound (p : State) (n : Nat) (ho : p.2%2=1) (h : longExcursion p n) :
    PhaseBlocks (fun i=>Uc (trace p (2*i))) (fun i=>Vc (trace p (2*i))) (sourceWord p n)
      (fun i=>phaseOf (trace p (2*i))) n := by
  unfold sourceWord
  rw [dite_eq_left ⟨ho,h⟩]
  exact Classical.choose_spec (tracePhasePrefix p n (2*n) ho h.1 h.2 (by omega)).2

 theorem trace_physical (p : State) (n : Nat) : Physical (fun i=>Uc (trace p (2*i))) (fun i=>Vc (trace p (2*i))) n := by
  intro i hi
  simp [Uc,Vc]
  omega

/-- A fiber of length k+1 ordinary blocks has a small diameter in the
    starting second counter, uniformly over the actual word. -/
theorem long_fiber_width (u x y R k : Nat) (hxy : x≤y)
    (hox : x%2=1) (hoy : y%2=1) (hph : phaseOf (u,x)=phaseOf (u,y))
    (hx : x<2*u+3) (hR : 2*u+x≤R)
    (hLx : longExcursion (u,x) (k+1)) (hLy : longExcursion (u,y) (k+1))
    (he : ∀ i, i<k+1 → sourceWord (u,x) (k+1) i=sourceWord (u,y) (k+1) i) :
    y-x≤(R+14*(k+1))/(2*4^k) := by
  let U := fun i=>Uc (trace (u,x) (2*i))
  let V := fun i=>Vc (trace (u,x) (2*i))
  let U' := fun i=>Uc (trace (u,y) (2*i))
  let V' := fun i=>Vc (trace (u,y) (2*i))
  let e := sourceWord (u,x) (k+1)
  let f := sourceWord (u,y) (k+1)
  have hs := sourceWord_sound (u,x) (k+1) hox hLx
  have hs' := sourceWord_sound (u,y) (k+1) hoy hLy
  have hU0 : U 0=Uc (u,x) := rfl
  have hV0 : V 0=Vc (u,x) := rfl
  have hV0' : V' 0=Vc (u,y) := rfl
  have hUeq : U 0=U' 0 := rfl
  have hd := phase_word_difference U V U' V' e f _ _ (k+1) hUeq (by simpa [trace,run] using hph) hs hs' he (k+1) (by omega)
  have hp := trace_physical (u,x) (k+1) (k+1) (by omega)
  have hp' := trace_physical (u,y) (k+1) (k+1) (by omega)
  change 18≤U (k+1) ∧ U (k+1)≤V (k+1)+18 at hp
  change 18≤U' (k+1) ∧ U' (k+1)≤V' (k+1)+18 at hp'
  have hb := phase_rank_bound U V e _ (k+1) hs (k+1) (by omega)
  have hfirst := first_digit u x U V e _ (k+1) (by omega) hx hU0 hV0 hs (trace_physical _ _)
  have hpow := word4_first_bound e k hfirst
  have hdelta : V' 0-V 0=3*((y-x:Nat):Int) := by rw [hV0,hV0']; simp [Vc,Int.natCast_sub hxy]; omega
  rw [hdelta] at hd
  have hh : (2:Int)*4^k*(3*((y-x:Nat):Int))≤2*word4 e (k+1)*(3*((y-x:Nat):Int)) := by
    apply Int.mul_le_mul_of_nonneg_right _ (by omega)
    omega
  have hp0 : 0<(2:Int)*4^k := Int.mul_pos (by decide) (Int.pow_pos (by decide))
  have hmul : (2:Int)*4^k*((y-x:Nat):Int)≤R+14*(k+1) := by
    rw [hV0] at hb
    simp [Vc] at hb
    have hv0 : 6*(u:Int)+3*(x:Int)≤3*(R:Int) := by omega
    push_cast at hh
    have hstep : (2:Int)*4^k*(3*((y-x:Nat):Int))=3*((2:Int)*4^k*((y-x:Nat):Int)) := by grind +ring
    rw [hstep] at hh
    push_cast at hb
    omega
  apply (Nat.le_div_iff_mul_le (Nat.mul_pos (by decide) (Nat.pow_pos (by decide)))).mpr
  have hm : ((y-x:Nat):Int)*((2:Int)*4^k)≤R+14*(k+1) := by rw [Int.mul_comm]; exact hmul
  exact_mod_cast hm

/-- Number of long post-burst starts at a fixed first counter, phase and
    rank cap. All possible branch words are covered. -/
theorem long_excursion_cardinality (u R k : Nat) (ph : Bool) (l : List Nat) (hn : l.Nodup)
    (hl : ∀ w∈l, w%2=1 ∧ phaseOf (u,w)=ph ∧ w<2*u+3 ∧ 2*u+w≤R ∧ longExcursion (u,w) (k+1)) :
    l.length≤2^k*((R+14*(k+1))/(2*4^k)+1) := by
  let e := fun w i=>sourceWord (u,w) (k+1) (i+1)
  apply binary_fiber_bound k _ l e hn
  intro xs hxs hnd he
  apply diameter_bound xs _ hnd
  intro x hx y hy hxy
  obtain ⟨ho,hph,hxg,hR,hL⟩ := hl x (hxs hx)
  obtain ⟨ho',hph',hyg,hR',hL'⟩ := hl y (hxs hy)
  apply long_fiber_width u x y R k hxy ho ho' (hph.trans hph'.symm) hxg hR hL hL'
  intro i hi
  cases i with
  | zero =>
    have hx0 := first_digit u x _ _ _ _ (k+1) (by omega) hxg rfl rfl (sourceWord_sound _ _ ho hL) (trace_physical _ _)
    have hy0 := first_digit u y _ _ _ _ (k+1) (by omega) hyg rfl rfl (sourceWord_sound _ _ ho' hL') (trace_physical _ _)
    exact hx0.trans hy0.symm
  | succ i => exact he x hx y hy i (by omega)

#print axioms long_excursion_cardinality

/-- A halt after i complete ordinary blocks, without any earlier section. -/
def haltAtBlock (p : State) (i : Nat) : Prop := longExcursion p i ∧ next (trace p (2*i))=none

 theorem halt_fiber_unique (u x y n : Nat) (hxy : x≤y) (hox : x%2=1) (hoy : y%2=1)
    (hph : phaseOf (u,x)=phaseOf (u,y)) (hx : haltAtBlock (u,x) n) (hy : haltAtBlock (u,y) n)
    (he : ∀ i, i<n → sourceWord (u,x) n i=sourceWord (u,y) n i) : x=y := by
  let U := fun i=>Uc (trace (u,x) (2*i))
  let V := fun i=>Vc (trace (u,x) (2*i))
  let U' := fun i=>Uc (trace (u,y) (2*i))
  let V' := fun i=>Vc (trace (u,y) (2*i))
  let e := sourceWord (u,x) n
  let f := sourceWord (u,y) n
  have hd := phase_word_difference U V U' V' e f _ _ n rfl (by simpa [trace,run] using hph)
    (sourceWord_sound _ _ hox hx.1) (sourceWord_sound _ _ hoy hy.1) he n (by omega)
  have hdelta : V' 0-V 0=3*((y:Int)-x) := by simp [V,V',trace,run,Vc]; omega
  rw [hdelta] at hd
  have hpos : 0≤2*word4 e n*(3*((y:Int)-x)) := Int.mul_nonneg (by have h := word4_bound e n; omega) (by omega)
  have hhalt : 2*U n=V n+39 := halt_equation _ hx.2
  have hhalt' : 2*U' n=V' n+39 := halt_equation _ hy.2
  omega

 theorem halt_at_zero_bound (u : Nat) (ph : Bool) (l : List Nat) (hn : l.Nodup)
    (hl : ∀ w∈l, w%2=1 ∧ phaseOf (u,w)=ph ∧ haltAtBlock (u,w) 0) : l.length≤1 := by
  apply diameter_bound l 0 hn
  intro x hx y hy hxy
  obtain ⟨hox,hpx,hhx⟩ := hl x hx
  obtain ⟨hoy,hpy,hhy⟩ := hl y hy
  have he := halt_fiber_unique u x y 0 hxy hox hoy (hpx.trans hpy.symm) hhx hhy (by omega)
  omega

 theorem halt_at_block_bound (u k : Nat) (ph : Bool) (l : List Nat) (hn : l.Nodup)
    (hl : ∀ w∈l, w%2=1 ∧ phaseOf (u,w)=ph ∧ w<2*u+3 ∧ haltAtBlock (u,w) (k+1)) : l.length≤2^k := by
  have hb : l.length≤2^k*1 := by
    let e := fun w i=>sourceWord (u,w) (k+1) (i+1)
    apply binary_fiber_bound k 1 l e hn
    intro xs hxs hnd he
    apply diameter_bound xs 0 hnd
    intro x hx y hy hxy
    obtain ⟨ho,hph,hxg,hL⟩ := hl x (hxs hx)
    obtain ⟨ho',hph',hyg,hL'⟩ := hl y (hxs hy)
    have h := halt_fiber_unique u x y (k+1) hxy ho ho' (hph.trans hph'.symm) hL hL' (by
      intro i hi
      cases i with
      | zero =>
        have hx0 := first_digit u x _ _ _ _ (k+1) (by omega) hxg rfl rfl (sourceWord_sound _ _ ho hL.1) (trace_physical _ _)
        have hy0 := first_digit u y _ _ _ _ (k+1) (by omega) hyg rfl rfl (sourceWord_sound _ _ ho' hL'.1) (trace_physical _ _)
        exact hx0.trans hy0.symm
      | succ i => exact he x hx y hy i (by omega))
    omega
  simpa using hb

 def earlyHalt (p : State) (n : Nat) : Prop := ∃ i, i<n ∧ haltAtBlock p i

/-- Exact cardinal upper bound on all halting leaves before depth k+1. -/
theorem early_halt_bound (u k : Nat) (ph : Bool) (l : List Nat) (hn : l.Nodup)
    (hl : ∀ w∈l, w%2=1 ∧ phaseOf (u,w)=ph ∧ w<2*u+3 ∧ earlyHalt (u,w) (k+1)) : l.length≤2^k := by
  classical
  induction k generalizing l with
  | zero =>
    apply halt_at_zero_bound u ph l hn
    intro w hw
    obtain ⟨ho,hph,hg,i,hi,hh⟩ := hl w hw
    have he : i=0 := by omega
    subst i
    exact ⟨ho,hph,hh⟩
  | succ k ih =>
    let f := fun w=>decide (earlyHalt (u,w) (k+1))
    let a := l.filter f
    let b := l.filter (fun w=> !f w)
    have ha : a.length≤2^k := by
      apply ih a (List.filter_sublist.nodup hn)
      intro w hw
      obtain ⟨hm,hf⟩ := List.mem_filter.mp hw
      have hh : earlyHalt (u,w) (k+1) := of_decide_eq_true hf
      obtain ⟨ho,hph,hg,_⟩ := hl w hm
      exact ⟨ho,hph,hg,hh⟩
    have hb : b.length≤2^k := by
      apply halt_at_block_bound u k ph b (List.filter_sublist.nodup hn)
      intro w hw
      obtain ⟨hm,hf⟩ := List.mem_filter.mp hw
      have hn' : ¬earlyHalt (u,w) (k+1) := by simpa [f] using hf
      obtain ⟨ho,hph,hg,i,hi,hh⟩ := hl w hm
      have he : i=k+1 := by
        by_cases hne : i=k+1
        · exact hne
        · exfalso
          exact hn' ⟨i,by omega,hh⟩
      subst i
      exact ⟨ho,hph,hg,hh⟩
    have ht : a.length+b.length=l.length := filter_split_len l f
    rw [Nat.pow_succ]
    omega

/-- No successful return to either section within N transitions. -/
def noReturn (p : State) (N : Nat) : Prop := ∀ k t, 0<k → k≤N → run k p=some t → ¬isSection t

 theorem noReturn_long_or_halt (p : State) (n : Nat) (ho : p.2%2=1) (hn : noReturn p (2*n)) :
    longExcursion p n ∨ earlyHalt p n := by
  induction n with
  | zero => left; exact ⟨good_zero p,by intro k hk hk'; omega⟩
  | succ n ih =>
    rcases ih (by intro k t hk hk' hr; exact hn k t hk (by omega) hr) with hlong|hearly
    · have hg := hlong.1
      by_cases hhalt : next (trace p (2*n))=none
      · right; exact ⟨n,by omega,hlong,hhalt⟩
      · have hg1 := good_next p (2*n) hg hhalt
        have hav : ¬isSection (trace p (2*n+1)) := hn _ _ (by omega) (by omega) (hg1 _ (by omega))
        have hodd := (tracePrefix p n (2*n) ho hg hlong.2 (by omega)).1 n (by omega)
        have heven := next_odd_to_even _ _ (good_step p (2*n+1) (2*n) hg1 (by omega)) hodd hav
        have hnot : next (trace p (2*n+1))≠none := by
          intro hh
          have hh' := halt_equation _ hh
          simp [Uc,Vc] at hh'
          omega
        have hg2 : good p (2*(n+1)) := by
          simpa only [show 2*n+1+1=2*(n+1) by omega] using good_next p (2*n+1) hg1 hnot
        left
        refine ⟨hg2,?_⟩
        intro k hk hk'
        exact hn k _ hk hk' (hg2 k hk')
    · right
      obtain ⟨i,hi,hh⟩ := hearly
      exact ⟨i,by omega,hh⟩

/-- All bad starts, including every actual halt before the next section at
    any time, are bounded by the early leaves plus the long fibers. -/
theorem no_return_cardinality (u R k : Nat) (ph : Bool) (l : List Nat) (hn : l.Nodup)
    (hl : ∀ w∈l, w%2=1 ∧ phaseOf (u,w)=ph ∧ w<2*u+3 ∧ 2*u+w≤R ∧ noReturn (u,w) (2*(k+1))) :
    l.length≤2^k*((R+14*(k+1))/(2*4^k)+2) := by
  classical
  let f := fun w=>decide (longExcursion (u,w) (k+1))
  let a := l.filter f
  let b := l.filter (fun w=> !f w)
  have ha : a.length≤2^k*((R+14*(k+1))/(2*4^k)+1) := by
    apply long_excursion_cardinality u R k ph a (List.filter_sublist.nodup hn)
    intro w hw
    obtain ⟨hm,hf⟩ := List.mem_filter.mp hw
    obtain ⟨ho,hph,hg,hR,_⟩ := hl w hm
    exact ⟨ho,hph,hg,hR,of_decide_eq_true hf⟩
  have hb : b.length≤2^k := by
    apply early_halt_bound u k ph b (List.filter_sublist.nodup hn)
    intro w hw
    obtain ⟨hm,hf⟩ := List.mem_filter.mp hw
    obtain ⟨ho,hph,hg,hR,hN⟩ := hl w hm
    have hn' : ¬longExcursion (u,w) (k+1) := by simpa [f] using hf
    exact ⟨ho,hph,hg,(noReturn_long_or_halt _ _ ho hN).resolve_left hn'⟩
  have ht : a.length+b.length=l.length := filter_split_len l f
  rw [show (R+14*(k+1))/(2*4^k)+2=(R+14*(k+1))/(2*4^k)+1+1 by omega,Nat.mul_add,Nat.mul_one]
  omega

#print axioms no_return_cardinality
end BB429.CoarseExit
