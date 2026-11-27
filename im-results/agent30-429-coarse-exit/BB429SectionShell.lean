import BB429SectionEntropy

namespace BB429.CoarseExit

private theorem filter_split_len' (l : List Nat) (p : Nat → Bool) :
    (l.filter p).length+(l.filter fun a=> !p a).length=l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : p a <;> simp [h] <;> omega

/-- Bound a finite family using a finite range of colors, with a bound on
    each monochromatic subfamily. -/
theorem color_fiber_bound (N M : Nat) (l : List Nat) (f : Nat → Nat) (hn : l.Nodup)
    (hf : ∀ w∈l, f w<N)
    (h : ∀ xs : List Nat, xs ⊆ l → xs.Nodup →
      (∀ x∈xs, ∀ y∈xs, f x=f y) → xs.length≤M) : l.length≤N*M := by
  induction N generalizing l with
  | zero =>
    cases l with
    | nil => simp
    | cons a as => have hh := hf a (by simp); omega
  | succ N ih =>
    let p := fun w=>decide (f w=N)
    let a := l.filter p
    let b := l.filter (fun w=> !p w)
    have ha : a.length≤M := by
      apply h a (by intro x hx; exact (List.mem_filter.mp hx).1) (List.filter_sublist.nodup hn)
      intro x hx y hy
      have h1 : f x=N := of_decide_eq_true (List.mem_filter.mp hx).2
      have h2 : f y=N := of_decide_eq_true (List.mem_filter.mp hy).2
      omega
    have hb : b.length≤N*M := by
      apply ih b (List.filter_sublist.nodup hn)
      · intro x hx
        obtain ⟨hm,he⟩ := List.mem_filter.mp hx
        have hne : f x≠N := by simpa [p] using he
        have hh := hf x hm
        omega
      · intro xs hxs hnd hsame
        exact h xs (by intro x hx; exact (List.mem_filter.mp (hxs hx)).1) hnd hsame
    have ht : a.length+b.length=l.length := filter_split_len' l p
    rw [Nat.succ_mul]
    omega

/-- A physically valid first-branch burst of length k, without any
    requirement that the endpoint itself can continue first-only. -/
def burstPossible (a W k : Nat) : Prop := 2*(a+3)*2^k≤2*a+W+3*k+6

def burstU (a k : Nat) : Nat := (a+3)*2^k-3

def burstW (a W k : Nat) : Nat := 2*a+W+3*k-2*burstU a k

theorem burstU_exact (a k : Nat) : burstU a k+3=(a+3)*2^k := by
  have hp : 3≤(a+3)*2^k := by
    have h := Nat.le_mul_of_pos_right (a+3) (Nat.pow_pos (a:=2) (n:=k) (by decide))
    omega
  simp [burstU]; omega

theorem burst_endpoint (a W k : Nat) (h : burstPossible a W k) :
    run k (a,W)=some (burstU a k,burstW a W k) ∧
    2*burstU a k+burstW a W k=2*a+W+3*k := by
  have hu := burstU_exact a k
  have h' : 2*burstU a k≤2*a+W+3*k := by
    unfold burstPossible at h
    rw [show 2*(a+3)*2^k=2*((a+3)*2^k) by grind +ring,←hu] at h
    omega
  have hr : 2*burstU a k+burstW a W k=2*a+W+3*k := by simp [burstW]; omega
  exact ⟨LowReturnBand.section_burst a k W _ _ hu hr,hr⟩

theorem burst_maximal (a W k : Nat) (h : burstPossible a W k) (hn : ¬burstPossible a W (k+1)) :
    burstW a W k<2*burstU a k+3 := by
  have hu := burstU_exact a k
  have hr := (burst_endpoint a W k h).2
  unfold burstPossible at hn
  rw [Nat.pow_succ,show 2*(a+3)*(2^k*2)=4*((a+3)*2^k) by grind +ring,←hu] at hn
  omega

private theorem pow_ge_add2 (k : Nat) (hk : 2≤k) : k+2≤2^k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h : 2≤k
    · have hh := ih h
      rw [Nat.pow_succ]
      omega
    · have he : k=1 := by omega
      subst k
      decide

private theorem burst_upper_impossible (a W n : Nat) (ha : a≤11) (hW : W<4^(n+1)) :
    ¬burstPossible a W (2*n+4) := by
  intro h
  have hp : 2^(2*n+4)=16*4^n := by
    rw [Nat.pow_add,Nat.pow_mul]
    change 4^n*16=16*4^n
    exact Nat.mul_comm ..
  have hk := pow_ge_add2 (2*n+4) (by omega)
  have hmul := Nat.mul_le_mul_right (2^(2*n+4)) (show 6≤2*(a+3) by omega)
  unfold burstPossible at h
  rw [Nat.pow_succ] at hW
  have hpos : 1≤4^n := Nat.pow_pos (by decide)
  omega

private theorem first_failure (P : Nat → Prop) (N : Nat) (h0 : P 0) (hN : ¬P N) :
    ∃ k, k<N ∧ P k ∧ ¬P (k+1) := by
  induction N with
  | zero => exact False.elim (hN h0)
  | succ N ih =>
    by_cases h : P N
    · exact ⟨N,by omega,h,hN⟩
    · obtain ⟨k,hk,hp,hn⟩ := ih h
      exact ⟨k,by omega,hp,hn⟩

/-- A maximal initial burst exists; in a base-four rank shell the length
    lies in an interval of only nine integers. -/
theorem shell_burst_exists (a W n : Nat) (ha : a≤11) (hlo : 4^n≤W) (hhi : W<4^(n+1)) :
    ∃ k, 2*n≤k+5 ∧ k≤2*n+3 ∧ burstPossible a W k ∧ ¬burstPossible a W (k+1) := by
  obtain ⟨k,hk,hp,hn⟩ := first_failure (burstPossible a W) (2*n+4) (by simp [burstPossible]; omega) (burst_upper_impossible a W n ha hhi)
  refine ⟨k,?_,by omega,hp,hn⟩
  by_cases he : 2*n≤k+5
  · exact he
  · exfalso
    have hpw := Nat.pow_le_pow_right (n:=2) (by decide) (show k+6≤2*n by omega)
    rw [Nat.pow_add,Nat.pow_mul] at hpw
    change 2^k*64≤4^n at hpw
    have hmul := Nat.mul_le_mul_right (2^k) (show 4*(a+3)≤56 by omega)
    have hpos : 1≤2^k := Nat.pow_pos (by decide)
    unfold burstPossible at hn
    rw [Nat.pow_succ,show 2*(a+3)*(2^k*2)=4*(a+3)*2^k by grind +ring] at hn
    omega

noncomputable def shellBurst (a W n : Nat) : Nat := by
  classical
  exact if h : a≤11 ∧ 4^n≤W ∧ W<4^(n+1) then Classical.choose (shell_burst_exists a W n h.1 h.2.1 h.2.2) else 0

theorem shellBurst_spec (a W n : Nat) (ha : a≤11) (hlo : 4^n≤W) (hhi : W<4^(n+1)) :
    2*n≤shellBurst a W n+5 ∧ shellBurst a W n≤2*n+3 ∧ burstPossible a W (shellBurst a W n) ∧
    ¬burstPossible a W (shellBurst a W n+1) := by
  unfold shellBurst
  rw [dite_eq_left ⟨ha,hlo,hhi⟩]
  exact Classical.choose_spec (shell_burst_exists a W n ha hlo hhi)

 theorem even_nonfirst_return (u w : Nat) (he : w%2=0) (hg : w<2*u+3) :
    ∃ t, next (u,w)=some t ∧ isSection t := by
  simp only [next]
  repeat' split
  all_goals first | omega | (refine ⟨_,rfl,?_⟩; simp [isSection])

 theorem noReturn_after_burst (a W n k : Nat) (hk : k≤2*n+3) (hp : burstPossible a W k)
    (hn : ¬burstPossible a W (k+1)) (hbad : noReturn (a,W) (4*n+5)) :
    (burstW a W k)%2=1 ∧ noReturn (burstU a k,burstW a W k) (2*(n+1)) := by
  have hb := burst_endpoint a W k hp
  have hnf := burst_maximal a W k hp hn
  have hnr : noReturn (burstU a k,burstW a W k) (2*(n+1)) := by
    intro i t hi hI hr
    apply hbad (k+i) t (by omega) (by omega)
    rw [run_add,hb.1,Option.bind_some,hr]
  refine ⟨?_,hnr⟩
  by_cases ho : (burstW a W k)%2=1
  · exact ho
  · obtain ⟨t,ht,hs⟩ := even_nonfirst_return (burstU a k) (burstW a W k) (by omega) hnf
    exact False.elim (hnr 1 t (by omega) (by omega) (by simpa [run] using ht) hs)

private theorem shell_growth (n : Nat) (hn : 3≤n) : 20*n+45<2*4^n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : 3≤n
    · have hh := ih h
      rw [Nat.pow_succ]
      omega
    · have he : n=2 := by omega
      subst n
      decide

 theorem postburst_shell_bound (u n : Nat) (hn : 3≤n) (ph : Bool) (l : List Nat) (hnd : l.Nodup)
    (hl : ∀ w∈l, w%2=1 ∧ phaseOf (u,w)=ph ∧ w<2*u+3 ∧ 2*u+w≤4^(n+1)+6*n+31 ∧ noReturn (u,w) (2*(n+1))) :
    l.length≤4*2^n := by
  have h := no_return_cardinality u (4^(n+1)+6*n+31) n ph l hnd hl
  have hg := shell_growth n hn
  have hd : (4^(n+1)+6*n+31+14*(n+1))/(2*4^n)≤2 := by
    apply (Nat.div_le_iff_le_mul_add_pred (Nat.mul_pos (by decide) (Nat.pow_pos (by decide)))).2
    rw [Nat.pow_succ]
    have hp : 1≤4^n := Nat.pow_pos (by decide)
    omega
  have hmul := Nat.mul_le_mul_left (2^n) (show (4^(n+1)+6*n+31+14*(n+1))/(2*4^n)+2≤4 by omega)
  omega

/-- All prepared inputs, for either fixed section, requiring more than
    4n+5 transitions to return (including ALL eventual first-excursion halts)
    number at most 72*2^n in the shell 4^n<=W<4^(n+1). -/
theorem section_shell_bad_bound (a n : Nat) (ha : a≤11) (hn : 3≤n) (l : List Nat) (hnd : l.Nodup)
    (hl : ∀ W∈l, 4^n≤W ∧ W<4^(n+1) ∧ noReturn (a,W) (4*n+5)) :
    l.length≤72*2^n := by
  let f := fun W => let k := shellBurst a W n; 2*(k+5-2*n)+(if phaseOf (burstU a k,burstW a W k) then 1 else 0)
  have hcolor : ∀ W∈l, f W<18 := by
    intro W hW
    obtain ⟨hlo,hhi,_⟩ := hl W hW
    have hs := shellBurst_spec a W n ha hlo hhi
    dsimp [f]
    split <;> omega
  have hc : l.length≤18*(4*2^n) := by
    apply color_fiber_bound 18 (4*2^n) l f hnd hcolor
    intro xs hsub hnd' hsame
    cases hxs : xs with
    | nil => simp
    | cons W rest =>
      have hw : W∈xs := by simp [hxs]
      let k := shellBurst a W n
      let u := burstU a k
      let ph := phaseOf (u,burstW a W k)
      obtain ⟨hlo,hhi,_⟩ := hl W (hsub hw)
      have hs := shellBurst_spec a W n ha hlo hhi
      have hsame' : ∀ Z∈xs, shellBurst a Z n=k ∧ phaseOf (u,burstW a Z k)=ph := by
        intro Z hz
        obtain ⟨hlo',hhi',_⟩ := hl Z (hsub hz)
        have hs' := shellBurst_spec a Z n ha hlo' hhi'
        have he := hsame Z hz W hw
        dsimp [f] at he
        have hk : shellBurst a Z n=k := by
          dsimp [k]
          split at he <;> split at he <;> omega
        rw [hk] at he
        refine ⟨hk,?_⟩
        dsimp [k,u,ph] at hk ⊢
        have hc : (if phaseOf (burstU a (shellBurst a W n),burstW a Z (shellBurst a W n)) then (1:Nat) else 0) =
            (if phaseOf (burstU a (shellBurst a W n),burstW a W (shellBurst a W n)) then 1 else 0) := by
          dsimp [k] at he
          omega
        cases h1 : phaseOf (burstU a (shellBurst a W n),burstW a Z (shellBurst a W n)) <;>
          cases h2 : phaseOf (burstU a (shellBurst a W n),burstW a W (shellBurst a W n)) <;> simp_all
      let ys := xs.map (fun Z=>burstW a Z k)
      have hm : ∀ Z∈xs, 2*u+burstW a Z k=2*a+Z+3*k := by
        intro Z hz
        obtain ⟨hlo',hhi',_⟩ := hl Z (hsub hz)
        have hs' := shellBurst_spec a Z n ha hlo' hhi'
        rw [(hsame' Z hz).1] at hs'
        exact (burst_endpoint a Z k hs'.2.2.1).2
      have hndY : ys.Nodup := by
        unfold ys
        rw [List.nodup_iff_pairwise_ne,List.pairwise_map]
        apply List.Pairwise.imp_of_mem (R:=fun x y=>x≠y) _ hnd'
        intro X Y hX hY hne he
        have hx := hm X hX
        have hy := hm Y hY
        exact hne (by omega)
      have hy : ∀ w∈ys, w%2=1 ∧ phaseOf (u,w)=ph ∧ w<2*u+3 ∧ 2*u+w≤4^(n+1)+6*n+31 ∧ noReturn (u,w) (2*(n+1)) := by
        intro w hw'
        obtain ⟨Z,hZ,rfl⟩ := List.mem_map.mp hw'
        obtain ⟨hlo',hhi',hbad⟩ := hl Z (hsub hZ)
        have hs' := shellBurst_spec a Z n ha hlo' hhi'
        have hsameZ := hsame' Z hZ
        rw [hsameZ.1] at hs'
        have hnr := noReturn_after_burst a Z n k hs'.2.1 hs'.2.2.1 hs'.2.2.2 hbad
        refine ⟨hnr.1,hsameZ.2,burst_maximal a Z k hs'.2.2.1 hs'.2.2.2,?_,hnr.2⟩
        have hh := hm Z hZ
        omega
      have hb := postburst_shell_bound u n hn ph ys hndY hy
      simpa [ys,hxs] using hb
  omega

#print axioms section_shell_bad_bound
end BB429.CoarseExit
