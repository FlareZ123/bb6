import CountedBMO5PairDrain
import CapMulti

namespace CountedBMO5Pair
open Counted421 (score arrivalCost arrival_edge score_pos fastScore_eq)

theorem none_persists {c : Cfg} {n m : Nat} (h : run n c=none) (hm : n≤m) : run m c=none := by
  rw [show m=n+(m-n) by omega,run_add,h]; rfl

theorem exact_none {c : Cfg} {n : Nat} (h : Exact c n none) : run n c=none := by
  obtain ⟨k,d,rfl,hr,hs⟩ := h
  rw [run_add,hr]
  simp [run,hs]

theorem exact_unique {c : Cfg} {n m : Nat} (h : Exact c n none) (h' : Exact c m none) : n=m := by
  have hn := exact_none h
  have hm := exact_none h'
  obtain ⟨k,d,hk,hr,_⟩ := h
  obtain ⟨l,e,hl,hr',_⟩ := h'
  by_cases hlt : n<m
  · have e := none_persists hn (show n≤l by omega)
    rw [hr'] at e; contradiction
  · by_cases hgt : m<n
    · have e := none_persists hm (show m≤k by omega)
      rw [hr] at e; contradiction
    · omega

theorem exact_split {c d : Cfg} {a n : Nat} (h : run a c=some d) (hh : Exact c n none) :
    ∃ m, n=a+m ∧ Exact d m none := by
  have hn := exact_none hh
  obtain ⟨k,e,hk,hr,hs⟩ := hh
  have ha : a≤k := by
    by_cases hgood : a≤k
    · exact hgood
    · have he := none_persists hn (show n≤a by omega)
      rw [h] at he; contradiction
  have he : run (k-a) d=some e := by
    rw [show k=a+(k-a) by omega,run_add,h] at hr
    exact hr
  exact ⟨k-a+1,by omega,⟨k-a,e,rfl,he,hs⟩⟩

theorem arrival_three : arrivalCost 3=0 := by rw [Counted421.arrivalCost]; rfl

theorem arrival_five : arrivalCost 5=39 := by
  rw [arrival_edge Cap.Edge.one,Counted421.arrivalCost,fastScore_eq]
  rfl

theorem arrival_segment {s x : Nat} (hs : 2≤s) (hr : Cap.Reach s x) :
    ∃ t, arrivalCost x=arrivalCost s+t ∧ run t (cfg s)=some (cfg x) := by
  induction hr with
  | refl => exact ⟨0,rfl,rfl⟩
  | @tail x y h e ih =>
    obtain ⟨t,ht,ht'⟩ := ih
    have he := section_success (by have := Cap.reach_le h; omega) (Cap.edge_iff.mp e)
    rw [←fastScore_eq] at he
    exact ⟨t+score x,by rw [arrival_edge e,ht,Nat.add_assoc],seq ht' he⟩

theorem halt_reaches_terminal {s x n : Nat} (hs : 2≤s) (hx : Cap.Reach s x) (hn : Exact (cfg x) n none) :
    ∃ y, Cap.Reach s y ∧ Cap.f y=none := by
  induction n using Nat.strongRecOn generalizing x with
  | ind n ih =>
    cases hf : Cap.f x with
    | none => exact ⟨x,hx,hf⟩
    | some y =>
      have he := section_success (by have := Cap.reach_le hx; omega) hf
      rw [←fastScore_eq] at he
      obtain ⟨m,hm,hex⟩ := exact_split he hn
      exact ih m (by have := score_pos x; omega) (.tail hx (Cap.edge_iff.mpr hf)) hex

/-- Common exact weighted terminal sum, including the terminal cost of #421. -/
def W (i : Nat) := arrivalCost (Cap.halt i)+score (Cap.halt i)

theorem reachable_halt252 {i : Nat} (hr : Cap.rootOf (Cap.halt i)=1) : Exact blank252 (W i+3) none := by
  have hi := Cap.halt_ge2 i
  have hh := (Cap.reach_five_iff (Cap.halt i) (by omega)).mpr hr
  obtain ⟨t,ht,ht'⟩ := arrival_segment (by decide : 2≤5) hh
  obtain ⟨u,hu,hu'⟩ := section_terminal hi ((Cap.f_none_iff hi).mpr ⟨i,rfl⟩)
  rw [←fastScore_eq] at hu
  rw [arrival_five] at ht
  have hstart : run 54 blank252=some (cfg 5) := init252
  have he := exact_seq (seq hstart ht') hu'
  have hn : 54+t+u=W i+3 := by unfold W; omega
  rwa [hn] at he

theorem reachable_halt754 {i : Nat} (hr : Cap.rootOf (Cap.halt i)=3) : Exact blank754 (W i+18) none := by
  have hi := Cap.halt_ge2 i
  have hh := (Cap.reach_from_root 3 (Cap.halt i) Cap.root_three).mpr hr
  obtain ⟨t,ht,ht'⟩ := arrival_segment (by decide : 2≤3) hh
  obtain ⟨u,hu,hu'⟩ := section_terminal hi ((Cap.f_none_iff hi).mpr ⟨i,rfl⟩)
  rw [←fastScore_eq] at hu
  rw [arrival_three] at ht
  have hstart : run 30 blank754=some (cfg 3) := init754
  have he := exact_seq (seq hstart ht') hu'
  have hn : 30+t+u=W i+18 := by unfold W; omega
  rwa [hn] at he

theorem exact252_iff (n : Nat) : Exact blank252 n none ↔ ∃ i, Cap.rootOf (Cap.halt i)=1 ∧ n=W i+3 := by
  constructor
  · intro h
    obtain ⟨m,_,hm⟩ := exact_split (show run 54 blank252=some (cfg 5) from init252) h
    obtain ⟨y,hy,hf⟩ := halt_reaches_terminal (by decide : 2≤5) Cap.Reach.refl hm
    obtain ⟨i,rfl⟩ := (Cap.f_none_iff (by have := Cap.reach_le hy; omega)).mp hf
    have hr := (Cap.reach_five_iff _ (by have := Cap.halt_ge2 i; omega)).mp hy
    exact ⟨i,hr,exact_unique h (reachable_halt252 hr)⟩
  · rintro ⟨i,hr,rfl⟩
    exact reachable_halt252 hr

theorem exact754_iff (n : Nat) : Exact blank754 n none ↔ ∃ i, Cap.rootOf (Cap.halt i)=3 ∧ n=W i+18 := by
  constructor
  · intro h
    obtain ⟨m,_,hm⟩ := exact_split (show run 30 blank754=some (cfg 3) from init754) h
    obtain ⟨y,hy,hf⟩ := halt_reaches_terminal (by decide : 2≤3) Cap.Reach.refl hm
    obtain ⟨i,rfl⟩ := (Cap.f_none_iff (by have := Cap.reach_le hy; omega)).mp hf
    have hr := (Cap.reach_from_root 3 _ Cap.root_three).mp hy
    exact ⟨i,hr,exact_unique h (reachable_halt754 hr)⟩
  · rintro ⟨i,hr,rfl⟩
    exact reachable_halt754 hr

-- State-conjugacy transfers the exact halt score to the literal #754 table.
def Exact754 (n : Nat) : Prop := ∃ k d, n=k+1 ∧ run754 k ⟨.A,0,0⟩=some d ∧ step754 d=none

theorem exact754_conjugate (n : Nat) : Exact754 n ↔ Exact blank754 n none := by
  constructor
  · rintro ⟨k,d,hn,hr,hh⟩
    have hc := run_conjugate k blank754
    change run754 k ⟨.A,0,0⟩=(run k blank754).map rename at hc
    rw [hr] at hc
    cases h : run k blank754 with
    | none => simp [h] at hc
    | some e =>
      have hde : d=rename e := by simpa [h] using hc
      subst d
      rw [step_conjugate] at hh
      have he : step e=none := by
        cases hs : step e with
        | none => rfl
        | some v => simp only [hs,Option.map_some,reduceCtorEq] at hh
      exact ⟨k,e,hn,h,he⟩
  · rintro ⟨k,d,hn,hr,hh⟩
    have hc := run_conjugate k blank754
    change run754 k ⟨.A,0,0⟩=(run k blank754).map rename at hc
    rw [hr] at hc
    exact ⟨k,rename d,hn,hc,by rw [step_conjugate,hh]; rfl⟩

theorem exact754_literal_iff (n : Nat) : Exact754 n ↔ ∃ i, Cap.rootOf (Cap.halt i)=3 ∧ n=W i+18 :=
  (exact754_conjugate n).trans (exact754_iff n)

#print axioms exact252_iff
#print axioms exact754_literal_iff
end CountedBMO5Pair
