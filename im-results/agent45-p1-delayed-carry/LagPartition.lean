import LagReverse
namespace BB6.Agent45.DelayedCarry

inductive EndTree where
  | leaf : Nat → EndTree
  | fork : EndTree → EndTree → EndTree

def EndTree.Has : EndTree → Nat → Prop
  | .leaf c,e => c=e
  | .fork t u,e => t.Has e ∨ u.Has e

def EndTree.bits : EndTree → Nat
  | .leaf c => 2^c
  | .fork t u => t.bits ||| u.bits

theorem EndTree.bit_of_has (t : EndTree) (e : Nat) (h : t.Has e) : t.bits.testBit e=true := by
  induction t with
  | leaf c => simp [Has] at h; subst c; exact Nat.testBit_two_pow_self
  | fork t u ih ih' =>
    rcases h with h|h
    · simp [bits,Nat.testBit_or,ih h]
    · simp [bits,Nat.testBit_or,ih' h]

abbrev Entry := Nat × EndTree

def EntryCover (es : List Entry) (a e : Nat) : Prop :=
  ∃ t, (a,t)∈es ∧ t.Has e

theorem cover_cons (a e b : Nat) (t : EndTree) (es : List Entry) :
    EntryCover ((b,t)::es) a e ↔ (a=b ∧ t.Has e) ∨ EntryCover es a e := by
  simp only [EntryCover,List.mem_cons,Prod.mk.injEq]
  constructor
  · rintro ⟨u,⟨rfl,rfl⟩|hm,hu⟩
    · exact Or.inl ⟨rfl,hu⟩
    · exact Or.inr ⟨u,hm,hu⟩
  · rintro (⟨rfl,ht⟩|⟨u,hm,hu⟩)
    · exact ⟨t,Or.inl ⟨rfl,rfl⟩,ht⟩
    · exact ⟨u,Or.inr hm,hu⟩

/-- Merge sorted streams, retaining all endpoint leaves at equal ancestors.
The fuel fallback is conservative; sortedness is needed for speed only. -/
def mergeEntries : Nat → List Entry → List Entry → List Entry
  | 0,xs,ys => xs++ys
  | _+1,[],ys => ys
  | _+1,xs,[] => xs
  | f+1,(a,t)::xs,(b,u)::ys =>
    if a<b then (a,t)::mergeEntries f xs ((b,u)::ys)
    else if b<a then (b,u)::mergeEntries f ((a,t)::xs) ys
    else (a,EndTree.fork t u)::mergeEntries f xs ys

theorem merge_cover (f : Nat) (xs ys : List Entry) (a e : Nat)
    (h : EntryCover xs a e ∨ EntryCover ys a e) : EntryCover (mergeEntries f xs ys) a e := by
  induction f generalizing xs ys with
  | zero =>
    unfold mergeEntries EntryCover at *
    rcases h with ⟨t,hm,ht⟩|⟨t,hm,ht⟩
    · exact ⟨t,List.mem_append_left _ hm,ht⟩
    · exact ⟨t,List.mem_append_right _ hm,ht⟩
  | succ f ih =>
    cases xs with
    | nil => simpa [mergeEntries,EntryCover] using h
    | cons x xs =>
      cases ys with
      | nil => simpa [mergeEntries,EntryCover] using h
      | cons y ys =>
        obtain ⟨b,t⟩ := x
        obtain ⟨c,u⟩ := y
        simp only [mergeEntries]
        split
        · rw [cover_cons] at h ⊢
          rcases h with (ht|hh)|hh
          · exact Or.inl ht
          · exact Or.inr (ih xs ((c,u)::ys) (Or.inl hh))
          · exact Or.inr (ih xs ((c,u)::ys) (Or.inr hh))
        · split
          · rw [cover_cons (a:=a) (e:=e) (b:=c)] at h ⊢
            rcases h with hh|(ht|hh)
            · exact Or.inr (ih ((b,t)::xs) ys (Or.inl hh))
            · exact Or.inl ht
            · exact Or.inr (ih ((b,t)::xs) ys (Or.inr hh))
          · have hbc : b=c := by omega
            subst c
            simp only [cover_cons,EndTree.Has] at h ⊢
            rcases h with (⟨rfl,ht⟩|hh)|(⟨rfl,hu⟩|hh)
            · exact Or.inl ⟨rfl,Or.inl ht⟩
            · exact Or.inr (ih xs ys (Or.inl hh))
            · exact Or.inl ⟨rfl,Or.inr hu⟩
            · exact Or.inr (ih xs ys (Or.inr hh))

def backOne (n B i : Nat) (es : List Entry) : List Entry :=
  let lo := es.filterMap fun p =>
    if 2*p.1+target n i B<n+i+3 then some (predecessor n B i p.1,p.2) else none
  let hi := es.filterMap fun p =>
    if 2*p.1+target n i B<n+i+3 then none else some (predecessor n B i p.1,p.2)
  mergeEntries (lo.length+hi.length) lo hi

theorem backOne_cover (n B i c e : Nat) (es : List Entry) (h : EntryCover es c e) :
    EntryCover (backOne n B i es) (predecessor n B i c) e := by
  obtain ⟨t,hm,ht⟩ := h
  unfold backOne
  apply merge_cover
  by_cases hh : 2*c+target n i B<n+i+3
  · left; refine ⟨t,List.mem_filterMap.mpr ⟨(c,t),hm,?_⟩,ht⟩
    simp [hh]
  · right; refine ⟨t,List.mem_filterMap.mpr ⟨(c,t),hm,?_⟩,ht⟩
    simp [hh]

def backGroups (n B s : Nat) : Nat → List Entry → List Entry
  | 0,es => es
  | k+1,es => backGroups n B s k (backOne n B (s+k) es)

theorem backGroups_cover (n B s k c e : Nat) (es : List Entry) (h : EntryCover es c e) :
    EntryCover (backGroups n B s k es) (rewind n B s k c) e := by
  induction k generalizing es c with
  | zero => exact h
  | succ k ih => exact ih _ _ (backOne_cover n B (s+k) c e es h)

def leafEntries (cs : List Nat) : List Entry := cs.map fun c => (c,EndTree.leaf c)

theorem leaf_cover (cs : List Nat) (c : Nat) (h : c∈cs) : EntryCover (leafEntries cs) c c := by
  exact ⟨EndTree.leaf c,List.mem_map.mpr ⟨c,h,rfl⟩,rfl⟩

#print axioms backGroups_cover
end BB6.Agent45.DelayedCarry
