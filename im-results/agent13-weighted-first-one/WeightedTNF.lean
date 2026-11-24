import SparseBlankDelay

namespace BB6.Agent13BlankDelay
open BB6Coverage

/-- Swap two arbitrary state labels, including when they coincide. -/
def swapStates (a b : Fin 6) : StatePerm where
  forward := fun s => if s=a then b else if s=b then a else s
  backward := fun s => if s=a then b else if s=b then a else s
  leftInverse := by intro s; revert s; revert b; revert a; decide
  rightInverse := by intro s; revert s; revert b; revert a; decide

@[simp] theorem swapStates_a (a b : Fin 6) : (swapStates a b).forward a=b := by
  simp [swapStates]

theorem swapStates_fixes (a b s : Fin 6) (ha : s≠a) (hb : s≠b) :
    (swapStates a b).forward s=s ∧ (swapStates a b).backward s=s := by
  simp [swapStates,ha,hb]

/-- The weighted score predicate transfers back along any root-fixing
    renaming. The incoming zero-prefix paths are renamed too. -/
theorem weighted_rename_back (B : Nat) (e : StatePerm) (m : Machine)
    (hroot : e.forward 0=0) (hf : zeroNext m 0=none)
    (h : WeightedBound B (renameTable e m)) : WeightedBound B m := by
  intro k d hk hd
  obtain ⟨s,hs⟩ := (mem_delays_iff hf).mp hd
  have hp := renamed_path e m hs
  rw [hroot] at hp
  have hh := rename_haltsAt_iff e m 0 k
  rw [hroot] at hh
  exact h k d (hh.mpr hk) ((mem_delays_iff (terminal_zero_next hp)).mpr ⟨_,hp⟩)

/-- All assigned rows and successor labels lie within the introduced
    prefix of state labels. This includes known halts, if present. -/
def TNFSupport (p : PartialMachine) (cut : Nat) : Prop :=
  ∀ s t, p s=some t → s.1.val<cut ∧ ∀ mv, t=some mv → mv.next.val<cut

theorem rename_compatible_unused (p : PartialMachine) (m : Machine) (cut : Nat)
    (a b : Fin 6) (ha : cut≤a.val) (hb : cut≤b.val)
    (hs : TNFSupport p cut) (hc : compatible p m) :
    compatible p (renameTable (swapStates a b) m) := by
  intro slot t ht
  obtain ⟨hslot,hmv⟩ := hs slot t ht
  have hn1 : slot.1≠a := by intro h; rw [h] at hslot; omega
  have hn2 : slot.1≠b := by intro h; rw [h] at hslot; omega
  have hback := (swapStates_fixes a b slot.1 hn1 hn2).2
  unfold renameTable
  rw [hback]
  have h := hc slot t ht
  rw [show (slot.1,slot.2)=slot from Prod.eta _,h]
  cases t with
  | none => rfl
  | some mv =>
    have hnext := hmv mv rfl
    have hna : mv.next≠a := by intro h; rw [h] at hnext; omega
    have hnb : mv.next≠b := by intro h; rw [h] at hnext; omega
    simp [renameMove,(swapStates_fixes a b mv.next hna hnb).1]

/-- Branch soundness for a TNF node: all existing labels are retained, and
    all fresh successors are represented by the least unused label. A halt
    branch is mandatory, because classification alone does not bound it. -/
theorem tnf_branch_sound (B cut : Nat) (p : PartialMachine) (slot : Slot)
    (hcut : 0<cut) (hs : TNFSupport p cut) (_hu : p slot=none)
    (hslot : slot.1.val<cut) (hf : p initialSlot=some (some ⟨true,true,1⟩))
    (hhalt : ∀ m, compatible (refine p slot none) m → WeightedBound B m)
    (hold : ∀ mv : Move, mv.next.val<cut → ∀ m,
      compatible (refine p slot (some mv)) m → WeightedBound B m)
    (hnew : ∀ q : Fin 6, q.val=cut → ∀ w r : Bool, ∀ m,
      compatible (refine p slot (some ⟨w,r,q⟩)) m → WeightedBound B m) :
    ∀ m, compatible p m → WeightedBound B m := by
  intro m hc
  cases ht : m slot with
  | none =>
    apply hhalt m
    intro s t h
    by_cases he : s=slot
    · subst s; simp [refine] at h; subst t; exact ht
    · exact hc s t (by simpa [refine,he] using h)
  | some mv =>
    by_cases hused : mv.next.val<cut
    · apply hold mv hused m
      intro s t h
      by_cases he : s=slot
      · subst s; simp [refine] at h; subst t; exact ht
      · exact hc s t (by simpa [refine,he] using h)
    · have hc6 : cut<6 := by have := mv.next.isLt; omega
      let q : Fin 6 := ⟨cut,hc6⟩
      let e := swapStates mv.next q
      have ha : cut≤mv.next.val := by omega
      have hb : cut≤q.val := Nat.le_refl _
      have hc' := rename_compatible_unused p m cut mv.next q ha hb hs hc
      have hn1 : slot.1≠mv.next := by intro h; rw [h] at hslot; omega
      have hn2 : slot.1≠q := by intro h; rw [h] at hslot; exact (Nat.lt_irrefl cut) hslot
      have hback := (swapStates_fixes mv.next q slot.1 hn1 hn2).2
      have ht' : renameTable e m slot=some ⟨mv.write,mv.right,q⟩ := by
        unfold renameTable
        rw [show e.backward slot.1=slot.1 from hback,show (slot.1,slot.2)=slot from Prod.eta _,ht]
        simp [renameMove,e]
      have hroot : e.forward 0=0 := by
        apply (swapStates_fixes mv.next q 0 ?_ ?_).1
        · intro h; have hv := congrArg Fin.val h; simp at hv; omega
        · intro h; have hv := congrArg Fin.val h; change 0=cut at hv; omega
      apply weighted_rename_back B e m hroot (firstOne_terminal p hf m hc)
      apply hnew q rfl mv.write mv.right (renameTable e m)
      intro s t h
      by_cases he : s=slot
      · subst s; simp [refine] at h; subst t; exact ht'
      · exact hc' s t (by simpa [refine,he] using h)

/-- Sparse ordinary-move semantics. The execution stops before its first
    unknown or known-halting query. Successful prefixes are exact for all
    compatible total completions. -/
def knownStep (p : PartialMachine) (c : Config) : Option Config :=
  ((p (readSlot c)).getD none).map (applyMove c)

def knownRun (p : PartialMachine) : Nat → Option Config
  | 0 => some blank
  | n+1 => (knownRun p n).bind (knownStep p)

theorem knownStep_sound (p : PartialMachine) (m : Machine) (hc : compatible p m)
    (c d : Config) (h : knownStep p c=some d) : rawStep m c=some d := by
  unfold knownStep at h
  cases he : p (readSlot c) with
  | none => simp [he] at h
  | some t =>
    simpa [rawStep,hc _ t he,he] using h

theorem knownRun_sound (p : PartialMachine) (m : Machine) (hc : compatible p m)
    (n : Nat) (c : Config) (h : knownRun p n=some c) : run m n blank=some c := by
  induction n generalizing c with
  | zero => exact h
  | succ n ih =>
    unfold knownRun at h
    cases he : knownRun p n with
    | none => simp [he] at h
    | some d =>
      rw [run,ih d he]
      exact knownStep_sound p m hc d c (by simpa [he] using h)

theorem knownRun_support (p : PartialMachine) (cut : Nat) (hcut : 0<cut)
    (hs : TNFSupport p cut) (n : Nat) (c : Config) (h : knownRun p n=some c) :
    c.state.val<cut := by
  induction n generalizing c with
  | zero =>
    change some blank=some c at h
    have hc : blank=c := Option.some.inj h
    subst c
    exact hcut
  | succ n ih =>
    unfold knownRun at h
    cases he : knownRun p n with
    | none => simp [he] at h
    | some d =>
      simp only [he,Option.bind_some,knownStep] at h
      cases hp : p (readSlot d) with
      | none => simp [hp] at h
      | some t =>
        cases t with
        | none => simp [hp] at h
        | some mv =>
          simp [hp] at h
          subst c
          exact (hs _ _ hp).2 mv rfl

theorem refine_preserves_compat (p : PartialMachine) (m : Machine) (slot : Slot) (t : Transition)
    (hu : p slot=none) (hc : compatible (refine p slot t) m) : compatible p m := by
  intro s v hv
  have he : s≠slot := by intro h; subst s; rw [hu] at hv; contradiction
  exact hc s v (by simp [refine,he,hv])

theorem refine_preserves_firstOne (p : PartialMachine) (slot : Slot) (t : Transition)
    (hu : p slot=none) (hf : p initialSlot=some (some ⟨true,true,1⟩)) :
    (refine p slot t) initialSlot=some (some ⟨true,true,1⟩) := by
  have he : initialSlot≠slot := by intro h; rw [h,hu] at hf; contradiction
  simp [refine,he,hf]

theorem refine_support (p : PartialMachine) (slot : Slot) (mv : Move) (cut cut' : Nat)
    (hs : TNFSupport p cut) (hle : cut≤cut') (hslot : slot.1.val<cut') (hmv : mv.next.val<cut') :
    TNFSupport (refine p slot (some mv)) cut' := by
  intro s t ht
  by_cases he : s=slot
  · subst s; simp [refine] at ht; subst t
    refine ⟨hslot,?_⟩
    intro v hv; cases hv; exact hmv
  · obtain ⟨h1,h2⟩ := hs s t (by simpa [refine,he] using ht)
    exact ⟨Nat.lt_of_lt_of_le h1 hle,fun v hv => Nat.lt_of_lt_of_le (h2 v hv) hle⟩

/-- If the sparse computation first encounters an undefined row at time n,
    the genuine-halt child has exactly n ordinary moves on every completion. -/
theorem first_hole_halts (p : PartialMachine) (n : Nat) (c : Config)
    (hr : knownRun p n=some c) (hu : p (readSlot c)=none)
    (m : Machine) (hc : compatible (refine p (readSlot c) none) m) : HaltsAfter m n := by
  have he := knownRun_sound p m (refine_preserves_compat p m _ _ hu hc) n c hr
  have ht := hc (readSlot c) none (by simp [refine])
  constructor
  · simp [he]
  · simp [run,he,rawStep,ht]

/-- A first-hole halt leaf is closed by a finite graph bound, without
    completing any of the other unknown rows. -/
theorem first_hole_weighted_halt (B : Nat) (p : PartialMachine) (n : Nat) (c : Config)
    (hf : p initialSlot=some (some ⟨true,true,1⟩))
    (hr : knownRun p n=some c) (hu : p (readSlot c)=none)
    (hd : ∀ d∈possibleDelays (refine p (readSlot c) none) 0, d+n+1≤B) :
    ∀ m, compatible (refine p (readSlot c) none) m → WeightedBound B m :=
  (uniform_halter_weight_iff _ _ _ (refine_preserves_firstOne p _ _ hu hf)
    (first_hole_halts p n c hr hu)).mpr hd

theorem all_ordinary_never (m : Machine) (h : ∀ slot, ∃ mv, m slot=some mv) : NeverHalts m := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    cases he : run m n blank with
    | none => simp [he] at ih
    | some c =>
      obtain ⟨mv,hm⟩ := h (readSlot c)
      simp [run,he,rawStep,hm]

theorem weighted_never (B : Nat) (m : Machine) (hn : NeverHalts m) : WeightedBound B m := by
  intro k d hk hd
  have he := hn (k+1)
  rw [hk.2] at he
  contradiction

/-- Exact justification of expand' at the last undefined row: every ordinary
    child has a total transition table and cannot halt. The halt child must
    still be accounted for at its weighted score. -/
theorem last_hole_sound (B : Nat) (p : PartialMachine) (n : Nat) (c : Config)
    (hf : p initialSlot=some (some ⟨true,true,1⟩))
    (hr : knownRun p n=some c) (hu : p (readSlot c)=none)
    (hrest : ∀ slot, slot≠readSlot c → ∃ mv, p slot=some (some mv))
    (hd : ∀ d∈possibleDelays (refine p (readSlot c) none) 0, d+n+1≤B) :
    ∀ m, compatible p m → WeightedBound B m := by
  intro m hc
  cases ht : m (readSlot c) with
  | none =>
    apply first_hole_weighted_halt B p n c hf hr hu hd m
    intro slot t hs
    by_cases he : slot=readSlot c
    · subst slot; simp [refine] at hs; subst t; exact ht
    · exact hc slot t (by simpa [refine,he] using hs)
  | some mv =>
    apply weighted_never B m
    apply all_ordinary_never m
    intro slot
    by_cases he : slot=readSlot c
    · subst slot; exact ⟨mv,ht⟩
    · obtain ⟨v,hv⟩ := hrest slot he
      exact ⟨v,hc slot _ hv⟩

/-- Certified normalized expansion at the actual first hole. The caller
    supplies only existing-label and least-fresh-label child proofs. -/
theorem first_hole_tnf_cover (B cut : Nat) (p : PartialMachine) (n : Nat) (c : Config)
    (hcut : 0<cut) (hs : TNFSupport p cut)
    (hf : p initialSlot=some (some ⟨true,true,1⟩))
    (hr : knownRun p n=some c) (hu : p (readSlot c)=none)
    (hd : ∀ d∈possibleDelays (refine p (readSlot c) none) 0, d+n+1≤B)
    (hold : ∀ mv : Move, mv.next.val<cut → ∀ m,
      compatible (refine p (readSlot c) (some mv)) m → WeightedBound B m)
    (hnew : ∀ q : Fin 6, q.val=cut → ∀ w r : Bool, ∀ m,
      compatible (refine p (readSlot c) (some ⟨w,r,q⟩)) m → WeightedBound B m) :
    Cover (WeightedBound B) p :=
  .leaf p (tnf_branch_sound B cut p (readSlot c) hcut hs hu
    (knownRun_support p cut hcut hs n c hr) hf
    (first_hole_weighted_halt B p n c hf hr hu hd) hold hnew)

#print axioms weighted_rename_back
#print axioms tnf_branch_sound
#print axioms first_hole_weighted_halt
#print axioms last_hole_sound
#print axioms first_hole_tnf_cover
end BB6.Agent13BlankDelay
