import ReverseBlock
namespace BB6.Agent45ReverseBlock

theorem start_bound {F z ys c} (h : Walk F z ys c) : z<F := by
  induction h with
  | nil hz => exact hz
  | step _ _ _ _ _ _ _ _ _ _ _ ih => exact ih

/-- Compose in traversal order: ts is processed before ys. -/
theorem walk_append {F z ts d} (ht : Walk F z ts d) {ys c}
    (hy : Walk (F-ts.length) d ys c) : Walk F z (ys++ts) c := by
  induction hy with
  | nil hz => simpa using ht
  | step ys a y b r h hb hy hc hr he ih =>
    have hlen' : F-((ys++ts).length+1)=F-ts.length-(ys.length+1) := by simp; omega
    exact Walk.step (ys++ts) a y b r ih hb hy (by rw [hlen']; exact hc) (by rw [hlen']; exact hr) (by rw [hlen']; exact he)

/-- Split a reversed walk at an arbitrary target-word boundary. -/
theorem walk_split (F z : Nat) (ys ts : List Nat) (c : Nat)
    (h : Walk F z (ys++ts) c) : ∃ d, Walk F z ts d ∧ Walk (F-ts.length) d ys c := by
  induction ys generalizing c with
  | nil => exact ⟨c,h,Walk.nil (walk_bound h)⟩
  | cons y ys ih =>
    change Walk F z (y::(ys++ts)) c at h
    cases h with
    | step xs a v b r hp hv hb ha hr he =>
      obtain ⟨d,ht,hy⟩ := ih a hp
      have hlen' : F-((ys++ts).length+1)=F-ts.length-(ys.length+1) := by simp; omega
      exact ⟨d,ht,Walk.step ys a y b c hy hv hb (by rw [← hlen']; exact ha) (by rw [← hlen']; exact hr) (by rw [← hlen']; exact he)⟩

/-- Push a single first reverse step before a previously established walk. -/
theorem prepend {F d ys c} (h : Walk F d ys c) (z y b : Nat)
    (hz : z<F) (hd : d<F) (hy : y≤1) (hb : b≤1)
    (he : 2*z+y=d+F*b) : Walk (F+1) z (ys++[y]) c := by
  have h0 : Walk (F+1) z [y] d := by
    apply Walk.step [] z y b d (Walk.nil (by omega)) hy hb <;> simpa
  exact walk_append h0 (by simpa using h)

/-- Exact image under a fitted block, arbitrary input order and duplicates. -/
def blockImage (F : Nat) (ys ends : List Nat) : List Nat :=
    ends.filterMap (fun z => fast F ys.length (2^ys.length*z+digits ys))

theorem mem_blockImage (F c : Nat) (ys ends : List Nat)
    (hys : ∀ y∈ys,y≤1) (hfit : 2^(ys.length+1)≤F) :
    c∈blockImage F ys ends ↔ ∃ z∈ends, Walk F z ys c := by
  simp only [blockImage,List.mem_filterMap]
  constructor
  · rintro ⟨z,hz,hf⟩
    exact ⟨z,hz,(fast_iff_walk F z ys c hys hfit).mp hf⟩
  · rintro ⟨z,hz,hw⟩
    exact ⟨z,hz,(fast_iff_walk F z ys c hys hfit).mpr hw⟩

/-- The block schedule is in forward chronological order. -/
def Fitted (q : Nat) : List (List Nat) → Prop
  | [] => True
  | ys::bs => 2^(ys.length+1)≤q+ys.length ∧ Fitted (q+ys.length) bs

def blockFold (q : Nat) : List (List Nat) → List Nat → List Nat
  | [],ends => ends.filter (·<q)
  | ys::bs,ends => blockImage (q+ys.length) ys (blockFold (q+ys.length) bs ends)

theorem mem_blockFold (q c : Nat) (bs : List (List Nat)) (ends : List Nat)
    (hys : ∀ y∈bs.flatten,y≤1) (hf : Fitted q bs) :
    c∈blockFold q bs ends ↔ ∃ z∈ends, Walk (q+bs.flatten.length) z bs.flatten c := by
  induction bs generalizing q c with
  | nil =>
    simp only [blockFold,List.flatten_nil,List.length_nil,Nat.add_zero,List.mem_filter,decide_eq_true_eq]
    constructor
    · rintro ⟨hc,hb⟩; exact ⟨c,hc,Walk.nil hb⟩
    · rintro ⟨z,hz,hw⟩; cases hw; exact ⟨hz,by assumption⟩
  | cons ys bs ih =>
    obtain ⟨hfit,hft⟩ := hf
    have hy : ∀ y∈ys,y≤1 := by intro y h; exact hys y (by simp [h])
    have hbs : ∀ y∈bs.flatten,y≤1 := by intro y h; exact hys y (by simp [h])
    rw [blockFold,mem_blockImage _ _ _ _ hy hfit]
    have hclock : q+(ys++bs.flatten).length=(q+ys.length)+bs.flatten.length := by simp [Nat.add_assoc]
    constructor
    · rintro ⟨d,hd,hw⟩
      obtain ⟨z,hz,ht⟩ := (ih (q+ys.length) d hbs hft).mp hd
      have hclock' : q+ys.length+bs.flatten.length-bs.flatten.length=q+ys.length := by omega
      have hw' : Walk (q+ys.length+bs.flatten.length-bs.flatten.length) d ys c := by simpa [hclock'] using hw
      exact ⟨z,hz,by simpa [Nat.add_assoc] using walk_append ht hw'⟩
    · rintro ⟨z,hz,hw⟩
      have hw' : Walk (q+ys.length+bs.flatten.length) z (ys++bs.flatten) c := by simpa [Nat.add_assoc] using hw
      obtain ⟨d,ht,hp⟩ := walk_split _ _ _ _ _ hw'
      have hclock' : q+ys.length+bs.flatten.length-bs.flatten.length=q+ys.length := by omega
      exact ⟨d,(ih (q+ys.length) d hbs hft).mpr ⟨z,hz,ht⟩,by simpa [hclock'] using hp⟩

#print axioms walk_append
#print axioms walk_split
#print axioms prepend
#print axioms mem_blockFold
end BB6.Agent45ReverseBlock
