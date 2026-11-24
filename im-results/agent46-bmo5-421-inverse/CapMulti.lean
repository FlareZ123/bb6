import CapRoot

namespace Cap

/-- A nonempty finite computation, ending in the given optional result. -/
inductive RunsTo {S : Type} (step : S → Option S) : S → Option S → Prop where
  | one (s : S) : RunsTo step s (step s)
  | head {s t : S} {res : Option S} : step s=some t → RunsTo step t res → RunsTo step s res

theorem RunsTo.of_eq {S : Type} {step : S → Option S} {s : S} {r : Option S}
    (h : step s=r) : RunsTo step s r := by rw [←h]; exact .one s

/-- The common even-counter fragment of the #252 and #754 source maps. -/
structure TripleRules {S : Type} (step : S → Option S) (mk : Nat → Nat → Nat → S) : Prop where
  zero : ∀ b, step (mk 0 b 0)=some (mk 0 1 (2*b+10))
  zeroSucc : ∀ a b, step (mk (a+1) b 0)=some (mk a b 1)
  one : ∀ a b, step (mk a b 1)=some (mk 0 1 (4*a+2*b+14))
  halt : ∀ a, step (mk a 0 2)=none
  four : ∀ a, step (mk a 0 4)=some (mk 0 1 (2*a+12))
  restart : ∀ a c, step (mk a 0 (c+6))=some (mk 0 (a+4) c)
  diag : ∀ a b c, step (mk a (b+1) (c+2))=some (mk (a+2) b c)

def sectionEncode {S : Type} (mk : Nat → Nat → Nat → S) (x : Nat) := mk 0 1 (2*(x-2))

theorem diagonal {S : Type} {step : S → Option S} {mk : Nat → Nat → Nat → S}
    (R : TripleRules step mk) (k a b c : Nat) {res : Option S}
    (h : RunsTo step (mk (a+2*k) b c) res) :
    RunsTo step (mk a (b+k) (c+2*k)) res := by
  induction k generalizing a with
  | zero => simpa using h
  | succ k ih =>
    have he := R.diag a (b+k) (c+2*k)
    have he1 : c+2*(k+1)=c+2*k+2 := by omega
    have he2 : a+2*(k+1)=a+2+2*k := by omega
    rw [he2] at h
    rw [he1,Nat.add_succ]
    exact .head he (ih (a+2) h)

theorem drain_triple {S : Type} {step : S → Option S} {mk : Nat → Nat → Nat → S}
    (R : TripleRules step mk) (r b : Nat) :
    RunsTo step (mk 0 b (2*r)) ((drain r b).map (sectionEncode mk)) := by
  induction r using Nat.strongRecOn generalizing b with
  | ind r ih =>
    rw [drain]
    by_cases h : r≤b
    · rw [if_pos h,Option.map_some]
      have hd : RunsTo step (mk (2*r) (b-r) 0) (some (sectionEncode mk (3*r+b+7))) := by
        by_cases hr : r=0
        · subst r
          simp [sectionEncode]
          apply RunsTo.of_eq
          rw [show 2*(b+5)=2*b+10 by omega]
          exact R.zero b
        · have ha : 2*r=(2*r-1)+1 := by omega
          rw [ha]
          apply RunsTo.head (R.zeroSucc (2*r-1) (b-r))
          apply RunsTo.of_eq
          unfold sectionEncode
          rw [show 2*(3*r+b+7-2)=4*(2*r-1)+2*(b-r)+14 by omega]
          exact R.one (2*r-1) (b-r)
      have hh := diagonal R r 0 (b-r) 0 (by simpa using hd)
      simpa [show b-r+r=b by omega] using hh
    · rw [if_neg h]
      by_cases he : r=b+1
      · rw [if_pos he,Option.map_none]
        have hh := diagonal R b 0 0 2 (by simpa using (RunsTo.of_eq (R.halt (2*b))))
        simpa [show 2*r=2+2*b by omega] using hh
      · rw [if_neg he]
        by_cases he2 : r=b+2
        · rw [if_pos he2,Option.map_some]
          have hd : RunsTo step (mk (2*b) 0 4) (some (sectionEncode mk (2*b+8))) := by
            apply RunsTo.of_eq
            unfold sectionEncode
            rw [show 2*(2*b+8-2)=2*(2*b)+12 by omega]
            exact R.four (2*b)
          have hh := diagonal R b 0 0 4 (by simpa using hd)
          simpa [show 2*r=4+2*b by omega] using hh
        · rw [if_neg he2]
          have hd : RunsTo step (mk (2*b) 0 (2*(r-b)))
              ((drain (r-b-3) (2*b+4)).map (sectionEncode mk)) := by
            rw [show 2*(r-b)=2*(r-b-3)+6 by omega]
            exact .head (R.restart (2*b) (2*(r-b-3))) (ih _ (by omega) _)
          have hh := diagonal R b 0 0 (2*(r-b)) (by simpa using hd)
          simpa [show 2*(r-b)+2*b=2*r by omega] using hh

theorem triple_transport {S : Type} {step : S → Option S} {mk : Nat → Nat → Nat → S}
    (R : TripleRules step mk) (x : Nat) (hx : 2≤x) :
    RunsTo step (sectionEncode mk x) ((f x).map (sectionEncode mk)) := by
  unfold f
  simp only [show x≠0 by omega, show x≠1 by omega,ite_false]
  exact drain_triple R (x-2) 1

-- Use a total natural-number domain for the common sectionEncode x>=2.
def sectionNext (n : Nat) : Option Nat := (f (n+2)).map (·-2)

theorem sectionNext_eq (n : Nat) : (sectionNext n).map (·+2)=f (n+2) := by
  unfold sectionNext
  cases h : f (n+2) with
  | none => simp
  | some x =>
    have hg := edge_grows (edge_iff.mpr h)
    simp [show x-2+2=x by omega]

theorem triple_section {S : Type} {step : S → Option S} {mk : Nat → Nat → Nat → S}
    (R : TripleRules step mk) (n : Nat) :
    RunsTo step (mk 0 1 (2*n)) ((sectionNext n).map (fun k=>mk 0 1 (2*k))) := by
  have h := triple_transport R (n+2) (by omega)
  unfold sectionEncode at h
  rw [←sectionNext_eq n] at h
  simpa [Option.map_map,Function.comp_def] using h

-- The three roots are distinct even though all share the same partial map.
theorem root_one : rootOf 1=1 := by rw [rootOf]; rfl
theorem root_three : rootOf 3=3 := by rw [rootOf]; rfl
theorem root_five : rootOf 5=1 := by rw [rootOf]; exact root_one

theorem reach_from_root (s x : Nat) (hs : rootOf s=s) : Reach s x ↔ rootOf x=s := by
  constructor
  · intro h; rw [root_reach h,hs]
  · intro h; have hr := root_reaches x; rw [h] at hr; exact hr

theorem from_one (x : Nat) (h : Reach 1 x) : x=1 ∨ Reach 5 x := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail x y h e ih =>
    rcases ih with he|hr
    · subst x
      have h := edge_iff.mp e
      have heq : f 1=some 5 := by decide
      rw [heq] at h
      have he := Option.some.inj h
      subst y
      exact Or.inr .refl
    · exact Or.inr (.tail hr e)

theorem reach_five_iff (x : Nat) (hx : x≠1) : Reach 5 x ↔ rootOf x=1 := by
  constructor
  · intro h; rw [root_reach h,root_five]
  · intro h
    have hr := (reach_from_root 1 x root_one).mpr h
    exact (from_one x hr).resolve_left hx

def haltsAtRoot (s : Nat) : Prop := ∃ x, Reach s x ∧ f x=none

theorem halt_ge2 (i : Nat) : 2≤halt i := by unfold halt; have := lo_ge i; omega

theorem root_terminal_criterion (s : Nat) (hs : 2≤s) (hroot : rootOf s=s) :
    haltsAtRoot s ↔ ∃ i, rootOf (halt i)=s := by
  constructor
  · rintro ⟨x,hr,hf⟩
    obtain ⟨i,rfl⟩ := (f_none_iff (by have := reach_le hr; omega)).mp hf
    exact ⟨i,(reach_from_root s _ hroot).mp hr⟩
  · rintro ⟨i,hr⟩
    exact ⟨halt i,(reach_from_root s _ hroot).mpr hr,(f_none_iff (halt_ge2 i)).mpr ⟨i,rfl⟩⟩

theorem halt_from_five : haltsAtRoot 5 ↔ ∃ i, rootOf (halt i)=1 := by
  constructor
  · rintro ⟨x,hr,hf⟩
    obtain ⟨i,rfl⟩ := (f_none_iff (by have := reach_le hr; omega)).mp hf
    exact ⟨i,(reach_five_iff _ (by have := halt_ge2 i; omega)).mp hr⟩
  · rintro ⟨i,hr⟩
    exact ⟨halt i,(reach_five_iff _ (by have := halt_ge2 i; omega)).mpr hr,
      (f_none_iff (halt_ge2 i)).mpr ⟨i,rfl⟩⟩

theorem halt_from_three : haltsAtRoot 3 ↔ ∃ i, rootOf (halt i)=3 :=
  root_terminal_criterion 3 (by decide) root_three

theorem halt_from_two : haltsAtRoot 2 ↔ ∃ i, rootOf (halt i)=2 :=
  root_terminal_criterion 2 (by decide) root_two

theorem roots_disjoint {s t x : Nat} (h : rootOf s≠rootOf t) :
    ¬(Reach s x ∧ Reach t x) := by
  rintro ⟨hs,ht⟩
  exact h ((root_reach hs).symm.trans (root_reach ht))

theorem reach_prepend {s t x : Nat} (e : Edge s t) (r : Reach t x) : Reach s x := by
  induction r with
  | refl => exact .tail .refl e
  | tail r e' ih => exact .tail ih e'

theorem section_edge {s t : Nat} (e : sectionNext s=some t) : Edge (s+2) (t+2) := by
  have h := sectionNext_eq s
  rw [e] at h
  exact edge_iff.mpr h.symm

theorem section_none {s : Nat} (e : sectionNext s=none) : f (s+2)=none := by
  have h := sectionNext_eq s
  rw [e] at h
  exact h.symm

def sectionResult (s : Nat) : Option Nat → Prop
  | none => haltsAtRoot (s+2)
  | some t => Reach (s+2) (t+2)

theorem section_runs {s : Nat} {res : Option Nat} (h : RunsTo sectionNext s res) :
    sectionResult s res := by
  induction h with
  | one s =>
    cases h : sectionNext s with
    | none => exact ⟨s+2,.refl,section_none h⟩
    | some t => exact .tail .refl (section_edge h)
  | @head s t res e r ih =>
    have he := section_edge e
    cases res with
    | none =>
      obtain ⟨x,hr,hf⟩ := ih
      exact ⟨x,reach_prepend he hr,hf⟩
    | some x => exact reach_prepend he ih

theorem section_edge_reverse {s t : Nat} (e : Edge s t) (hs : 2≤s) :
    sectionNext (s-2)=some (t-2) := by
  unfold sectionNext
  rw [Nat.sub_add_cancel hs,edge_iff.mp e]
  rfl

theorem reach_runs {s x : Nat} (hr : Reach s x) (hs : 2≤s) {res : Option Nat}
    (h : RunsTo sectionNext (x-2) res) : RunsTo sectionNext (s-2) res := by
  induction hr with
  | refl => exact h
  | tail r e ih =>
    apply ih
    have hle := reach_le r
    exact .head (section_edge_reverse e (by omega)) h

theorem section_halts (s : Nat) : RunsTo sectionNext s none ↔ haltsAtRoot (s+2) := by
  constructor
  · exact section_runs
  · rintro ⟨x,hr,hf⟩
    have hx := reach_le hr
    have hN : sectionNext (x-2)=none := by
      unfold sectionNext
      rw [Nat.sub_add_cancel (by omega : 2≤x),hf]
      rfl
    have hh := reach_runs hr (by omega) (RunsTo.of_eq hN)
    simpa using hh

#print axioms triple_transport
#print axioms triple_section
#print axioms halt_from_five
#print axioms halt_from_three
#print axioms roots_disjoint
#print axioms section_halts
end Cap
