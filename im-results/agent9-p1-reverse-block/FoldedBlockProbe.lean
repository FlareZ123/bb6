import BatchCarry

namespace BB6.Agent9FoldedProbe
open BB6.Agent9BatchCarry (Interior Edge Walk)

def complement (q c : Nat) : Nat := q-2-c
def fold (q c : Nat) : Nat := min c (complement q c)

theorem complement_interior {q c : Nat} (hc : Interior q c) :
    Interior q (complement q c) := by
  unfold Interior complement at *
  omega

theorem complement_involution {q c : Nat} (hc : Interior q c) :
    complement q (complement q c)=c := by
  unfold complement Interior at *
  omega

theorem fold_interior {q c : Nat} (hc : Interior q c) :
    Interior q (fold q c) := by
  have ht := complement_interior hc
  unfold fold
  by_cases h : c≤complement q c
  · simpa [Nat.min_eq_left h] using hc
  · have h' : complement q c≤c := by omega
    simpa [Nat.min_eq_right h'] using ht

theorem fold_complement {q c : Nat} (hc : Interior q c) :
    fold q (complement q c)=fold q c := by
  unfold fold
  rw [complement_involution hc, Nat.min_comm]

theorem fold_cases (q c : Nat) : fold q c=c ∨ fold q c=complement q c := by
  unfold fold
  by_cases h : c≤complement q c
  · exact Or.inl (Nat.min_eq_left h)
  · exact Or.inr (Nat.min_eq_right (by omega))

theorem fold_idempotent {q c : Nat} (hc : Interior q c) :
    fold q (fold q c)=fold q c := by
  rcases fold_cases q c with h|h
  · exact congrArg (fold q) h
  · exact (congrArg (fold q) h).trans (fold_complement hc)

theorem edge_complement {q c z : Nat} (h : Edge q c z) :
    Edge q (complement q c) (complement (q+1) z) := by
  obtain ⟨hc,hz,he⟩ := h
  refine ⟨complement_interior hc,complement_interior hz,?_⟩
  unfold complement Interior at *
  rcases he with he|he <;> omega

theorem walk_start {q c k z : Nat} (h : Walk q c k z) : Interior q c := by
  cases h with
  | nil q c hc => exact hc
  | cons q c d k z he ht => exact he.1

theorem walk_end {q c k z : Nat} (h : Walk q c k z) : Interior (q+k) z := by
  induction h with
  | nil q c hc => simpa using hc
  | cons q c d k z he ht ih =>
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih

theorem walk_complement {q c k z : Nat} (h : Walk q c k z) :
    Walk q (complement q c) k (complement (q+k) z) := by
  induction h with
  | nil q c hc => exact Walk.nil q _ (complement_interior hc)
  | cons q c d k z he ht ih =>
    have hh := Walk.cons q _ _ k _ (edge_complement he) ih
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem walk_append {q c k z : Nat} (h : Walk q c k z)
    {j w : Nat} (ht : Walk (q+k) z j w) : Walk q c (k+j) w := by
  induction h with
  | nil q c hi => simpa using ht
  | cons q c d k z he hs ih =>
    have hh : Walk (q+1+k) z j w := by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht
    have htail := ih hh
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Walk.cons q c d (k+j) w he htail

theorem walk_split (q c k j w : Nat) (h : Walk q c (k+j) w) :
    ∃ z, Walk q c k z ∧ Walk (q+k) z j w := by
  induction k generalizing q c with
  | zero =>
    simp only [Nat.zero_add,Nat.add_zero] at h ⊢
    exact ⟨c,Walk.nil q c (walk_start h),h⟩
  | succ k ih =>
    have hh : Walk q c (k+j+1) w := by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
    cases hh with
    | cons q c d len w he ht =>
      obtain ⟨z,h1,h2⟩ := ih (q+1) d ht
      exact ⟨z,Walk.cons q c d k z he h1,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h2⟩

/-- Canonical representatives, with the strict interval included. -/
def Canon (q c : Nat) : Prop := Interior q c ∧ fold q c=c

theorem canon_fold {q c : Nat} (hc : Interior q c) : Canon q (fold q c) :=
  ⟨fold_interior hc,fold_idempotent hc⟩

/-- A folded path is an ordinary path with its two endpoints folded. -/
def FoldedWalk (q a k b : Nat) : Prop :=
  ∃ c z, Walk q c k z ∧ fold q c=a ∧ fold (q+k) z=b

theorem folded_start {q a k b : Nat} (h : FoldedWalk q a k b) : Canon q a := by
  obtain ⟨c,z,hw,ha,hb⟩ := h
  rw [←ha]
  exact canon_fold (walk_start hw)

theorem folded_end {q a k b : Nat} (h : FoldedWalk q a k b) : Canon (q+k) b := by
  obtain ⟨c,z,hw,ha,hb⟩ := h
  rw [←hb]
  exact canon_fold (walk_end hw)

/-- Any folded path has a lift beginning at its canonical start. -/
theorem folded_lift_start {q a k b : Nat} (h : FoldedWalk q a k b) :
    ∃ z, Walk q a k z ∧ fold (q+k) z=b := by
  obtain ⟨c,z,hw,ha,hb⟩ := h
  rcases fold_cases q c with h|h
  · have hac : a=c := by omega
    exact ⟨z,by simpa [hac] using hw,hb⟩
  · have hac : a=complement q c := by omega
    refine ⟨complement (q+k) z,?_,?_⟩
    · simpa [hac] using walk_complement hw
    · rw [fold_complement (walk_end hw),hb]

/-- A lift can equally be chosen to end at the canonical endpoint. -/
theorem folded_lift_end {q a k b : Nat} (h : FoldedWalk q a k b) :
    ∃ c, Walk q c k b ∧ fold q c=a := by
  obtain ⟨c,z,hw,ha,hb⟩ := h
  rcases fold_cases (q+k) z with h|h
  · have hbz : b=z := by omega
    exact ⟨c,by simpa [hbz] using hw,ha⟩
  · have hbz : b=complement (q+k) z := by omega
    refine ⟨complement q c,?_,?_⟩
    · simpa [hbz] using walk_complement hw
    · rw [fold_complement (walk_start hw),ha]

theorem folded_iff_start {q a k b : Nat} (ha : Canon q a) :
    FoldedWalk q a k b ↔ ∃ z, Walk q a k z ∧ fold (q+k) z=b := by
  exact ⟨folded_lift_start,fun ⟨z,hw,hb⟩ => ⟨a,z,hw,ha.2,hb⟩⟩

theorem folded_append {q a k b j w : Nat} (h : FoldedWalk q a k b)
    (ht : FoldedWalk (q+k) b j w) : FoldedWalk q a (k+j) w := by
  obtain ⟨c,hc,ha⟩ := folded_lift_end h
  obtain ⟨z,hz,hb⟩ := folded_lift_start ht
  refine ⟨c,z,walk_append hc hz,ha,?_⟩
  simpa [Nat.add_assoc] using hb

theorem folded_split {q a k j w : Nat} (h : FoldedWalk q a (k+j) w) :
    ∃ b, FoldedWalk q a k b ∧ FoldedWalk (q+k) b j w := by
  obtain ⟨c,z,hw,ha,hb⟩ := h
  obtain ⟨d,h1,h2⟩ := walk_split q c k j z hw
  exact ⟨fold (q+k) d,⟨c,d,h1,ha,rfl⟩,⟨d,z,h2,rfl,by simpa [Nat.add_assoc] using hb⟩⟩

/-- One forward probe step, keeping both even numerators and folding. -/
def children (q a : Nat) : List Nat :=
  (([a,a+q].filter (fun v => v%2=0)).map (fun v => fold (q+1) (v/2))).eraseDups

theorem mem_children {q a b : Nat} (ha : Canon q a) :
    b∈children q a ↔ FoldedWalk q a 1 b := by
  rw [folded_iff_start ha]
  simp only [children,List.mem_eraseDups,List.mem_map,List.mem_filter,decide_eq_true_eq,List.mem_cons,List.not_mem_nil,or_false]
  constructor
  · rintro ⟨v,⟨hv,he⟩,hb⟩
    have heq : 2*(v/2)=v := by omega
    have hz : Interior (q+1) (v/2) := by
      have hc := ha.1
      unfold Interior at hc ⊢
      rcases hv with hv|hv <;> omega
    have hedge : Edge q a (v/2) := ⟨ha.1,hz,by rcases hv with hv|hv <;> omega⟩
    exact ⟨v/2,Walk.cons q a _ 0 _ hedge (Walk.nil _ _ hz),hb⟩
  · rintro ⟨z,hw,hb⟩
    cases hw with
    | cons q a d k z he ht =>
      cases ht
      obtain ⟨hc,hd,heq⟩ := he
      exact ⟨2*z,⟨heq,by omega⟩,by simpa using hb⟩

/-- Small forward image of a folded start; only these probes need scalar steps. -/
def forward (q a : Nat) : Nat → List Nat
  | 0 => [a]
  | k+1 => ((children q a).flatMap (fun b => forward (q+1) b k)).eraseDups

theorem mem_forward {q a k b : Nat} (ha : Canon q a) :
    b∈forward q a k ↔ FoldedWalk q a k b := by
  induction k generalizing q a with
  | zero =>
    rw [folded_iff_start ha]
    simp only [forward,List.mem_singleton,Nat.add_zero]
    constructor
    · intro h; subst b; exact ⟨a,Walk.nil q a ha.1,ha.2⟩
    · rintro ⟨z,hw,hz⟩; cases hw; exact hz.symm.trans ha.2
  | succ k ih =>
    simp only [forward,List.mem_eraseDups,List.mem_flatMap]
    constructor
    · rintro ⟨d,hd,hb⟩
      have h1 := (mem_children ha).1 hd
      have h2 := (ih (folded_end h1)).1 hb
      simpa [Nat.add_comm] using folded_append h1 h2
    · intro hw
      have hw' : FoldedWalk q a (1+k) b := by simpa [Nat.add_comm] using hw
      obtain ⟨d,h1,h2⟩ := folded_split hw'
      exact ⟨d,(mem_children ha).2 h1,(ih (folded_end h1)).2 h2⟩

/-- An abstract folded live set represents precisely paths to a common clock. -/
def LiveCover (q j : Nat) (ends : List Nat) : Prop :=
  ∀ b, b∈ends ↔ ∃ w, FoldedWalk q b j w

/-- Exact in-block probe. All central births in a skipped reverse block are
    recovered by these short forward intersections. -/
theorem probe_iff (q a k j : Nat) (ends : List Nat) (ha : Canon q a)
    (hends : LiveCover (q+k) j ends) :
    (∃ b∈forward q a k, b∈ends) ↔ ∃ z, Walk q a (k+j) z := by
  constructor
  · rintro ⟨b,hb,he⟩
    have h1 := (mem_forward ha).1 hb
    obtain ⟨w,h2⟩ := (hends b).1 he
    obtain ⟨z,hz,_⟩ := folded_lift_start (folded_append h1 h2)
    exact ⟨z,hz⟩
  · rintro ⟨z,hz⟩
    have hw : FoldedWalk q a (k+j) (fold (q+(k+j)) z) := ⟨a,z,hz,ha.2,rfl⟩
    obtain ⟨b,h1,h2⟩ := folded_split hw
    exact ⟨b,(mem_forward ha).2 h1,(hends b).2 ⟨_,h2⟩⟩

theorem center_canon (q : Nat) (hq : 4≤q) : Canon q ((q-2)/2) := by
  unfold Canon Interior fold complement
  constructor
  · omega
  · apply Nat.min_eq_left; omega

/-- At clocks divisible by four the center is odd and cannot make its first
    zero-target step, so positive-horizon probes need only clocks 2 mod 4. -/
theorem no_center_at_multiple_four (q k z : Nat) (hq : q%4=0) (hk : 0<k) :
    ¬ Walk q ((q-2)/2) k z := by
  intro hw
  have hi := walk_start hw
  unfold Interior at hi
  cases hw with
  | nil => omega
  | cons q a d k z he ht =>
    obtain ⟨_,_,he⟩ := he
    rcases he with he|he <;> omega

/-- Folding an exact reverse image of a folded live cover gives a new live
    cover, with no need to keep the noncanonical representative. -/
theorem folded_back_cover (q k j : Nat) (ends raw : List Nat)
    (hends : LiveCover (q+k) j ends)
    (hraw : ∀ c, c∈raw ↔ ∃ z∈ends, Walk q c k z) :
    LiveCover q (k+j) ((raw.map (fold q)).eraseDups) := by
  intro a
  simp only [List.mem_eraseDups,List.mem_map]
  constructor
  · rintro ⟨c,hc,ha⟩
    obtain ⟨z,hz,hw⟩ := (hraw c).1 hc
    obtain ⟨w,ht⟩ := (hends z).1 hz
    have h1 : FoldedWalk q a k z := ⟨c,z,hw,ha,(folded_start ht).2⟩
    exact ⟨w,folded_append h1 ht⟩
  · rintro ⟨w,hw⟩
    obtain ⟨b,h1,h2⟩ := folded_split hw
    obtain ⟨c,hc,ha⟩ := folded_lift_end h1
    exact ⟨c,(hraw c).2 ⟨b,(hends b).2 ⟨w,h2⟩,hc⟩,ha⟩

#print axioms folded_back_cover
#print axioms walk_complement
#print axioms folded_append
#print axioms folded_split
#print axioms mem_forward
#print axioms probe_iff
#print axioms no_center_at_multiple_four
end BB6.Agent9FoldedProbe
