import FoldedBlockProbe

namespace BB6.Agent43BirthLocate
open BB6.Agent9BatchCarry (Interior Edge Walk edge_iff_parent)
open BB6.Agent9FoldedProbe

/-- A fixed canonical terminal carry has at most one folded predecessor. -/
theorem one_parent {q a b : Nat} (h : FoldedWalk q a 1 b) :
    a = fold q ((2*b)%q) := by
  obtain ⟨c,hw,hc⟩ := folded_lift_end h
  cases hw with
  | cons q c d k y he ht =>
    cases ht
    have hp := (edge_iff_parent q c b he.2.1).1 he
    rw [←hc,hp.2]

/-- Every canonical terminal carry except the maximal one has a strict
    predecessor. This holds at odd clocks too, where the maximal class
    consists of two complementary, noncentral carries. -/
theorem parent_exists_iff (q b : Nat) (hb : Canon (q+1) b) :
    (∃ a, FoldedWalk q a 1 b) ↔ b < (q-1)/2 := by
  have hi := hb.1
  have hf := hb.2
  unfold Interior at hi
  unfold fold complement at hf
  have hle : b ≤ (q-1)/2 := by
    have hh := Nat.min_le_right b (q+1-2-b)
    rw [hf] at hh
    omega
  have hlt : 2*b<q := by omega
  constructor
  · rintro ⟨a,hw⟩
    obtain ⟨c,hc,_⟩ := folded_lift_end hw
    cases hc with
    | cons q c d k y he ht =>
      cases ht
      have hp := (edge_iff_parent q c b he.2.1).1 he
      rw [Nat.mod_eq_of_lt hlt] at hp
      unfold Interior at hp
      omega
  · intro h
    have hc : Interior q (2*b) := by unfold Interior; omega
    have he : Edge q (2*b) b := ⟨hc,hb.1,Or.inl rfl⟩
    have hw : Walk q (2*b) 1 b := Walk.cons q _ _ 0 _ he (Walk.nil _ _ hb.1)
    exact ⟨fold q (2*b),2*b,b,hw,rfl,hb.2⟩

/-- Reverse determinism is retained after quotienting by complement. -/
theorem unique_start {q a a' k b : Nat} (h : FoldedWalk q a k b)
    (h' : FoldedWalk q a' k b) : a=a' := by
  induction k generalizing q a a' with
  | zero =>
    obtain ⟨c,z,hw,ha,hb⟩ := h
    obtain ⟨c',z',hw',ha',hb'⟩ := h'
    cases hw
    cases hw'
    simp only [Nat.add_zero] at hb hb'
    omega
  | succ k ih =>
    have h1 : FoldedWalk q a (1+k) b := by simpa [Nat.add_comm] using h
    have h2 : FoldedWalk q a' (1+k) b := by simpa [Nat.add_comm] using h'
    obtain ⟨d,hp,ht⟩ := folded_split h1
    obtain ⟨d',hp',ht'⟩ := folded_split h2
    have hd := ih ht ht'
    subst d'
    exact (one_parent hp).trans (one_parent hp').symm

/-- Earliest surviving suffix of a fixed terminal class: the last strict
    predecessor is exactly the maximal folded class. -/
theorem first_failure_iff (q k z : Nat) :
    FoldedWalk (q+1) ((q-1)/2) k z ↔
      (∃ a, FoldedWalk (q+1) a k z) ∧ ¬ (∃ a, FoldedWalk q a (k+1) z) := by
  constructor
  · intro h
    refine ⟨⟨_,h⟩,?_⟩
    rintro ⟨a,hw⟩
    have hw' : FoldedWalk q a (1+k) z := by simpa [Nat.add_comm] using hw
    obtain ⟨d,hp,ht⟩ := folded_split hw'
    have hd := unique_start ht h
    subst d
    have hc := (parent_exists_iff q _ (folded_start h)).1 ⟨a,hp⟩
    omega
  · rintro ⟨⟨a,hw⟩,hn⟩
    have hc := folded_start hw
    have hle : a≤(q-1)/2 := by
      have hh := Nat.min_le_right a (q+1-2-a)
      have he := hc.2
      unfold fold complement at he
      rw [he] at hh
      omega
    have heq : a=(q-1)/2 := by
      by_cases heq : a=(q-1)/2
      · exact heq
      · exfalso
        have hp := (parent_exists_iff q a hc).2 (by omega)
        obtain ⟨b,hb⟩ := hp
        exact hn ⟨b,by simpa [Nat.add_comm] using folded_append hb hw⟩
    simpa [heq] using hw

/-- Existence of a strict folded suffix is downward closed in its length. -/
def HasSuffix (F z k : Nat) : Prop := ∃ c, FoldedWalk (F-k) c k z

theorem suffix_mono (F z k l : Nat) (hl : l≤k) (hk : k≤F)
    (h : HasSuffix F z k) : HasSuffix F z l := by
  obtain ⟨c,hc⟩ := h
  have hw : FoldedWalk (F-k) c (k-l+l) z := by simpa [Nat.sub_add_cancel hl] using hc
  obtain ⟨d,_,hd⟩ := folded_split hw
  exact ⟨d,by simpa [show F-k+(k-l)=F-l by omega] using hd⟩

/-- At an even clock q+1 the maximal folded class is the actual central
    birth. A single common-clock cover therefore identifies all skipped
    births by localizing failed predecessor queries, without forward probes. -/
theorem birth_from_failures (q k j : Nat) (ends : List Nat)
    (hends : LiveCover (q+1+k) j ends) (hq : 4≤q+1) :
    (∃ z, Walk (q+1) ((q-1)/2) (k+j) z) ↔
      ∃ b∈ends, (∃ a, FoldedWalk (q+1) a k b) ∧
        ¬ (∃ a, FoldedWalk q a (k+1) b) := by
  constructor
  · rintro ⟨z,hw⟩
    have hc : Canon (q+1) ((q-1)/2) := by
      simpa [show q+1-2=q-1 by omega] using center_canon (q+1) hq
    have hf : FoldedWalk (q+1) ((q-1)/2) (k+j) (fold (q+1+(k+j)) z) :=
      ⟨_,z,hw,hc.2,rfl⟩
    obtain ⟨b,hb,ht⟩ := folded_split hf
    exact ⟨b,(hends b).2 ⟨_,ht⟩,(first_failure_iff q k b).1 hb⟩
  · rintro ⟨b,hb,hf⟩
    have hw := (first_failure_iff q k b).2 hf
    obtain ⟨w,ht⟩ := (hends b).1 hb
    obtain ⟨z,hz,_⟩ := folded_lift_start (folded_append hw ht)
    exact ⟨z,hz⟩

#print axioms one_parent
#print axioms parent_exists_iff
#print axioms unique_start
#print axioms first_failure_iff
#print axioms suffix_mono
#print axioms birth_from_failures
end BB6.Agent43BirthLocate
