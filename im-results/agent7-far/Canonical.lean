import Symmetry
namespace BB6Coverage.Canonical

/-- Only already introduced states may occur anywhere in assigned rows. -/
def Scoped (k : Nat) (p : PartialMachine) : Prop :=
  ∀ s t, p s = some t → s.1.val < k ∧
    match t with
    | none => True
    | some mv => mv.next.val < k

def swap (a b x : Fin 6) : Fin 6 :=
  if x=a then b else if x=b then a else x

theorem swap_involution (a b x : Fin 6) : swap a b (swap a b x) = x := by
  by_cases hab : a=b
  · subst b
    simp [swap]
    split <;> simp_all
  · by_cases hxa : x=a
    · subst x; simp [swap,hab,Ne.symm hab]
    · by_cases hxb : x=b
      · subst x; simp [swap,hab,Ne.symm hab]
      · simp [swap,hxa,hxb]

def swapPerm (a b : Fin 6) : StatePerm :=
  ⟨swap a b,swap a b,swap_involution a b,swap_involution a b⟩
def idPerm : StatePerm := ⟨id,id,fun _ => rfl,fun _ => rfl⟩

def normPerm (k : Nat) (t : Transition) : StatePerm :=
  match t with
  | none => idPerm
  | some mv => if h : k ≤ mv.next.val then swapPerm mv.next ⟨k,by omega⟩ else idPerm

theorem normPerm_fixed (k : Nat) (t : Transition) (s : Fin 6) (hs : s.val < k) :
    (normPerm k t).forward s = s := by
  cases t with
  | none => rfl
  | some mv =>
    by_cases h : k ≤ mv.next.val
    · have h1 : s ≠ mv.next := by intro he; rw [he] at hs; omega
      have h2 : s ≠ (⟨k,by omega⟩ : Fin 6) := by intro he; have hv := congrArg Fin.val he; simp at hv; omega
      simp [normPerm,h,swapPerm,swap,h1,h2]
    · simp [normPerm,h,idPerm]

def normalize (k : Nat) (m : Machine) (s : Slot) : Machine :=
  renameTable (normPerm k (m s)) m

def canonChoices (k : Nat) : List Transition := choices.filter fun t =>
  match t with
  | none => true
  | some mv => decide (mv.next.val ≤ k)

def nextK (k : Nat) (t : Transition) : Nat :=
  match t with
  | none => k
  | some mv => max k (mv.next.val+1)

theorem normalize_slot (k : Nat) (m : Machine) (s : Slot) (hs : s.1.val < k) :
    normalize k m s s = (m s).map (renameMove (normPerm k (m s))) := by
  have hf := normPerm_fixed k (m s) s.1 hs
  have hb : (normPerm k (m s)).backward s.1 = s.1 := by
    have he := (normPerm k (m s)).leftInverse s.1
    rwa [hf] at he
  simp [normalize,renameTable,hb]

theorem normalize_choice (k : Nat) (m : Machine) (s : Slot) (hs : s.1.val < k) :
    normalize k m s s ∈ canonChoices k := by
  rw [normalize_slot k m s hs]
  apply List.mem_filter.mpr
  refine ⟨choices_complete _,?_⟩
  cases ht : m s with
  | none => rfl
  | some mv =>
    change decide (((normPerm k (some mv)).forward mv.next).val ≤ k) = true
    by_cases h : k ≤ mv.next.val
    · simp [normPerm,h,swapPerm,swap]
    · simp [normPerm,h,idPerm]
      omega

theorem normalize_compatible (k : Nat) (p : PartialMachine) (m : Machine)
    (s : Slot) (hp : Scoped k p) (hm : compatible p m) : compatible p (normalize k m s) := by
  intro slot t ht
  have hscope := hp slot t ht
  let e := normPerm k (m s)
  have hf : e.forward slot.1 = slot.1 := normPerm_fixed k (m s) _ hscope.1
  have hb : e.backward slot.1 = slot.1 := by
    have he := e.leftInverse slot.1
    rwa [hf] at he
  change (m (e.backward slot.1,slot.2)).map (renameMove e) = t
  rw [hb]
  have heq : (slot.1,slot.2) = slot := by cases slot; rfl
  rw [heq,hm slot t ht]
  cases t with
  | none => rfl
  | some mv =>
    have hn : e.forward mv.next = mv.next := normPerm_fixed k (m s) _ hscope.2
    simp [renameMove,hn]

theorem rename_decided_iff (e : StatePerm) (m : Machine) (bound : Nat)
    (hroot : e.forward 0 = 0) : DecidedBelow bound (renameTable e m) ↔ DecidedBelow bound m := by
  have hblank : renameConfig e blank = blank := by simp [renameConfig,blank,hroot]
  have hr (n : Nat) : run (renameTable e m) n blank = (run m n blank).map (renameConfig e) := by
    simpa only [hblank] using rename_run e m blank n
  have hn : NeverHalts (renameTable e m) ↔ NeverHalts m := by
    unfold NeverHalts
    constructor <;> intro h n <;> specialize h n
    · rw [hr] at h
      cases he : run m n blank <;> simp [he] at h ⊢
    · rw [hr]
      cases he : run m n blank <;> simp [he] at h ⊢
  have hh (n : Nat) : HaltsAfter (renameTable e m) n ↔ HaltsAfter m n := by
    unfold HaltsAfter
    rw [hr n,hr (n+1)]
    cases h1 : run m n blank <;> cases h2 : run m (n+1) blank <;> simp
  simp only [DecidedBelow,hn,hh]

theorem normalize_decided_iff (k bound : Nat) (m : Machine) (s : Slot) (hk : 0<k) :
    DecidedBelow bound (normalize k m s) ↔ DecidedBelow bound m :=
  rename_decided_iff _ m bound (normPerm_fixed k (m s) 0 hk)

theorem scoped_refine (k : Nat) (p : PartialMachine) (s : Slot) (t : Transition)
    (hp : Scoped k p) (hs : s.1.val < k) : Scoped (nextK k t) (refine p s t) := by
  have hle : k ≤ nextK k t := by cases t <;> simp [nextK] <;> omega
  intro slot u hu
  by_cases he : slot=s
  · subst slot
    have ht : t=u := by simpa [refine] using hu
    subst u
    refine ⟨by omega,?_⟩
    cases t <;> simp [nextK] <;> omega
  · have h := hp slot u (by simpa [refine,he] using hu)
    refine ⟨by omega,?_⟩
    cases u with
    | none => trivial
    | some mv => exact Nat.lt_of_lt_of_le h.2 hle

theorem nextK_bounds (k : Nat) (t : Transition) (hk : 0<k ∧ k≤6) : 0<nextK k t ∧ nextK k t≤6 := by
  cases t with
  | none => exact hk
  | some mv => simp [nextK]; omega

/-- Sound state-introduction reduction. Only existing states and the
    single least unused state are needed as transition targets. -/
theorem cover_branch (bound k : Nat) (p : PartialMachine) (s : Slot)
    (hp : Scoped k p) (hs : s.1.val < k) (hk : 0<k)
    (kids : ∀ t, t ∈ canonChoices k → Cover (DecidedBelow bound) (refine p s t)) :
    Cover (DecidedBelow bound) p := by
  apply Cover.leaf
  intro m hm
  let m' := normalize k m s
  have hcp := normalize_compatible k p m s hp hm
  have ht := normalize_choice k m s hs
  exact (normalize_decided_iff k bound m s hk).mp
    ((kids (m' s) ht).sound m' (compatible_refine p m' s hcp))

#print axioms cover_branch
end BB6Coverage.Canonical
