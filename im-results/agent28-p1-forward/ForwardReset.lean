import ForwardEven
namespace BB6.Agent28Forward
open BB6.Agent1 BB6P1Unit

/-- An arithmetic result has a genuine positive-length source walk to its odd hub,
    or a genuine finite source walk to a halted configuration. -/
def Realized (p : Nat × Nat) (out : Option (Nat × Nat)) : Prop :=
  match out with
  | none => ∃ n s, Walk p n s ∧ trans s=none
  | some (q,v) => valid q v ∧ ∃ n, 0<n ∧ Walk p n (decode q v)

theorem Realized.prepend {p r : Nat × Nat} {n : Nat} {out : Option (Nat × Nat)}
    (h : Walk p n r) (hr : Realized r out) : Realized p out := by
  cases out with
  | none =>
    obtain ⟨m,s,hw,hh⟩ := hr
    exact ⟨n+m,s,h.append hw,hh⟩
  | some o =>
    obtain ⟨hv,m,hm,hw⟩ := hr
    exact ⟨hv,n+m,by omega,h.append hw⟩

/-- Closed-form entire even excursion, including the possible second even reset.
    The largest admissible drop index is unique. -/
def resetRule (x : Nat) (out : Option (Nat × Nat)) : Prop :=
  ∃ j, drop j≤x ∧ x<drop (j+1) ∧
    let r:=x-drop j
    (r=0 ∧ out=some (A j-1,A j-6)) ∨
    (r=1 ∧ ∃ q v, Wrap (A j+j+1) (2*j+5) q v ∧ out=some (q,v)) ∨
    (r=2 ∧ out=none) ∨
    (3≤r ∧ ∃ q v, Wrap (A j+r-2) (2*r-1) q v ∧ out=some (q,v))

theorem resetRule_total (x : Nat) : ∃ out, resetRule x out ∧ Realized (2,2*x) out := by
  obtain ⟨j,hlo,hhi⟩ := phase_index x
  let r:=x-drop j
  have he : drop (j+1)=drop j+(A j-1) := rfl
  have hr : r<A j-1 := by dsimp [r]; omega
  have hA := A_lower j
  have hdrop := drop_identity j
  have hw := even_prefix x j hlo
  change Walk (2,2*x) (2*j) (evenHub j r) at hw
  by_cases hzero : r=0
  · refine ⟨some (A j-1,A j-6),⟨j,hlo,hhi,Or.inl ⟨hzero,rfl⟩⟩,?_⟩
    apply Realized.prepend hw
    rw [hzero]
    refine ⟨by unfold valid; omega,1,by decide,even_zero j⟩
  · by_cases hone : r=1
    · have hr2 : A j-4-drop j=j+3 := by omega
      have hp2 := even_prefix (A j-4) j (by omega)
      rw [hr2] at hp2
      obtain ⟨q,v,hwrap,hvalid,heven⟩ := even_small j (j+3) (by omega) (by omega)
      have hq : A j+(j+3)-2=A j+j+1 := by omega
      have hv : 2*(j+3)-1=2*j+5 := by omega
      rw [hq,hv] at hwrap
      refine ⟨some (q,v),⟨j,hlo,hhi,Or.inr (Or.inl ⟨hone,q,v,hwrap,rfl⟩)⟩,?_⟩
      apply Realized.prepend hw
      rw [hone]
      apply Realized.prepend (even_two j)
      apply Realized.prepend hp2
      exact ⟨hvalid,2,by decide,heven⟩
    · by_cases htwo : r=2
      · refine ⟨none,⟨j,hlo,hhi,Or.inr (Or.inr (Or.inl ⟨htwo,rfl⟩))⟩,?_⟩
        apply Realized.prepend hw
        rw [htwo]
        obtain ⟨p,hp,hh⟩ := even_halt j
        exact ⟨1,p,hp,hh⟩
      · obtain ⟨q,v,hwrap,hvalid,heven⟩ := even_small j r (by omega) hr
        exact ⟨some (q,v),⟨j,hlo,hhi,Or.inr (Or.inr (Or.inr ⟨by omega,q,v,hwrap,rfl⟩))⟩,
          Realized.prepend hw ⟨hvalid,2,by decide,heven⟩⟩

theorem resetRule_unique {x : Nat} {o p : Option (Nat × Nat)}
    (ho : resetRule x o) (hp : resetRule x p) : o=p := by
  obtain ⟨i,hi,hi',ho⟩ := ho
  obtain ⟨j,hj,hj',hp⟩ := hp
  have he := phase_index_unique x i j ⟨hi,hi'⟩ ⟨hj,hj'⟩
  subst j
  let r:=x-drop i
  change (r=0 ∧ o=some (A i-1,A i-6)) ∨
    (r=1 ∧ ∃ q v, Wrap (A i+i+1) (2*i+5) q v ∧ o=some (q,v)) ∨
    (r=2 ∧ o=none) ∨
    (3≤r ∧ ∃ q v, Wrap (A i+r-2) (2*r-1) q v ∧ o=some (q,v)) at ho
  change (r=0 ∧ p=some (A i-1,A i-6)) ∨
    (r=1 ∧ ∃ q v, Wrap (A i+i+1) (2*i+5) q v ∧ p=some (q,v)) ∨
    (r=2 ∧ p=none) ∨
    (3≤r ∧ ∃ q v, Wrap (A i+r-2) (2*r-1) q v ∧ p=some (q,v)) at hp
  rcases ho with h | h | h | h <;> rcases hp with hh | hh | hh | hh
  · exact h.2.trans hh.2.symm
  all_goals try (have := h.1; have := hh.1; omega)
  · obtain ⟨_,q,v,hwrap,rfl⟩ := h
    obtain ⟨_,q',v',hw',rfl⟩ := hh
    obtain ⟨rfl,rfl⟩ := hwrap.unique hw'
    rfl
  · exact h.2.trans hh.2.symm
  · obtain ⟨_,q,v,hwrap,rfl⟩ := h
    obtain ⟨_,q',v',hw',rfl⟩ := hh
    obtain ⟨rfl,rfl⟩ := hwrap.unique hw'
    rfl

theorem resetRule_sound {x : Nat} {out : Option (Nat × Nat)} (h : resetRule x out) :
    Realized (2,2*x) out := by
  obtain ⟨o,hr,hs⟩ := resetRule_total x
  rw [resetRule_unique h hr]
  exact hs

theorem resetRule_none_iff (x : Nat) : resetRule x none ↔ ∃ j, x=drop j+2 := by
  constructor
  · rintro ⟨j,hlo,hhi,hr⟩
    rcases hr with h | h | h | h
    · cases h.2
    · obtain ⟨_,q,v,hw,he⟩ := h
      cases he
    · exact ⟨j,by have := h.1; omega⟩
    · obtain ⟨_,q,v,hw,he⟩ := h
      cases he
  · rintro ⟨j,rfl⟩
    have hA := A_lower j
    have he : drop (j+1)=drop j+(A j-1) := rfl
    refine ⟨j,by omega,by omega,Or.inr (Or.inr (Or.inl ⟨by omega,rfl⟩))⟩

/-- The complete odd-hub return rule, using only increasing modulus, arithmetic
    resets, and one sparse terminal test. It contains no original G or T calls. -/
def Next (q v : Nat) (out : Option (Nat × Nat)) : Prop :=
  if v=0 then out=some (q+2,q-3)
  else if v=1 then resetRule (q-2) out
  else if v=2 then ∃ r w, Wrap q 4 r w ∧ out=some (r,w)
  else ∃ r w, Wrap q v r w ∧ out=some (r,w)

theorem next_total (q v : Nat) (h : valid q v) : ∃ out, Next q v out ∧ Realized (decode q v) out := by
  unfold valid at h
  by_cases hz : v=0
  · subst v
    refine ⟨some (q+2,q-3),by simp [Next],?_⟩
    exact ⟨by unfold valid; omega,2,by decide,right_one q (by omega)⟩
  · by_cases h1 : v=1
    · subst v
      obtain ⟨o,hr,hs⟩ := resetRule_total (q-2)
      exact ⟨o,by simpa [Next] using hr,Realized.prepend (right_three q (by omega)) hs⟩
    · by_cases h2 : v=2
      · subst v
        obtain ⟨r,w,hw,hv,hs⟩ := right_five q (by omega)
        exact ⟨some (r,w),by unfold Next; exact ⟨r,w,hw,rfl⟩,⟨hv,2,by decide,hs⟩⟩
      · obtain ⟨r,w,hw,hv,hs⟩ := regular_odd q v h (by omega)
        exact ⟨some (r,w),by simp only [Next,hz,h1,h2,if_false]; exact ⟨r,w,hw,rfl⟩,⟨hv,2,by decide,hs⟩⟩

theorem next_unique {q v : Nat} {o p : Option (Nat × Nat)} (ho : Next q v o) (hp : Next q v p) : o=p := by
  unfold Next at ho hp
  split at ho <;> rename_i h0
  · simp only [h0,if_true] at hp
    exact ho.trans hp.symm
  · simp only [h0,if_false] at hp
    split at ho <;> rename_i h1
    · simp only [h1,if_true] at hp
      exact resetRule_unique ho hp
    · simp only [h1,if_false] at hp
      split at ho <;> rename_i h2
      · simp only [h2,if_true] at hp
        obtain ⟨r,w,hw,rfl⟩ := ho
        obtain ⟨r',w',hw',rfl⟩ := hp
        obtain ⟨rfl,rfl⟩ := hw.unique hw'
        rfl
      · simp only [h2,if_false] at hp
        obtain ⟨r,w,hw,rfl⟩ := ho
        obtain ⟨r',w',hw',rfl⟩ := hp
        obtain ⟨rfl,rfl⟩ := hw.unique hw'
        rfl

theorem next_sound {q v : Nat} {out : Option (Nat × Nat)} (h : valid q v) (hn : Next q v out) :
    Realized (decode q v) out := by
  obtain ⟨o,hr,hs⟩ := next_total q v h
  rw [next_unique hn hr]
  exact hs

theorem next_none_iff (q v : Nat) (h : valid q v) :
    Next q v none ↔ v=1 ∧ ∃ j, q=7*2^j-j-3 := by
  unfold valid at h
  by_cases he : v=1
  · subst v
    simp only [Next,show (1:Nat)≠0 by decide,if_false,if_true,true_and]
    rw [resetRule_none_iff]
    constructor
    · rintro ⟨j,hj⟩
      have hd := drop_identity j
      unfold A at hd
      exact ⟨j,by omega⟩
    · rintro ⟨j,hj⟩
      have hd := drop_identity j
      unfold A at hd
      exact ⟨j,by omega⟩
  · simp only [he,false_and,iff_false]
    by_cases h0 : v=0
    · simp [Next,h0]
    · by_cases h2 : v=2
      · simp [Next,h0,he,h2]
      · simp [Next,h0,he,h2]

#print axioms resetRule_total
#print axioms resetRule_unique
#print axioms next_total
#print axioms next_sound
#print axioms next_none_iff
end BB6.Agent28Forward
