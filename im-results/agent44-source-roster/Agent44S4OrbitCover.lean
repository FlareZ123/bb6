/-!
Agent 44: finite S4 safety-cover diagnostic.

State labels are A..F = Fin 6, symbols are 0..1 = Fin 2, and a
transition is (write, direction, next-state).  `refines child parent`
means that `child` assigns every transition already assigned by `parent`;
thus the cylinder of `child` is contained in the cylinder of `parent`.

The first theorem states the correct sufficient condition for a symmetry
quotient: each residual's symmetry image must refine a proved representative.
The concrete q32 example shows why exact roster closure cannot be assumed.
-/

universe u v

/-- Safety of a representative covers any symmetry image that refines it. -/
theorem all_safe_of_orbit_cover
    {P : Type u} {G : Type v}
    (act : G → P → P)
    (refines : P → P → Prop)
    (safe : P → Prop)
    (safe_mono : ∀ {child parent}, refines child parent → safe parent → safe child)
    (safe_transport : ∀ g x, safe x → safe (act g x))
    (inv : ∀ g, ∃ gInv, ∀ x, act gInv (act g x) = x)
    (xs reps : List P)
    (cover : ∀ x, x ∈ xs → ∃ g r, r ∈ reps ∧ refines (act g x) r)
    (reps_safe : ∀ r, r ∈ reps → safe r) :
    ∀ x, x ∈ xs → safe x := by
  intro x hx
  rcases cover x hx with ⟨g, r, hr, hrefines⟩
  have hq : safe (act g x) := safe_mono hrefines (reps_safe r hr)
  rcases inv g with ⟨gInv, hInv⟩
  have hback : safe (act gInv (act g x)) := safe_transport gInv (act g x) hq
  simpa [hInv x] using hback

inductive Dir where
  | L | R
  deriving DecidableEq, Repr

abbrev State := Fin 6
abbrev Bit := Fin 2

structure Move where
  write : Bit
  dir : Dir
  next : State
  deriving DecidableEq, Repr

abbrev PartialTable := State → Bit → Option Move

-- q32 is A0=1RB, B0=1RC, C0=0LA.
def q32 : PartialTable := fun q b =>
  if q = 0 ∧ b = 0 then some ⟨1, .R, 1⟩
  else if q = 1 ∧ b = 0 then some ⟨1, .R, 2⟩
  else if q = 2 ∧ b = 0 then some ⟨0, .L, 0⟩
  else none

-- The three broader cylinders containing the nontrivial q32 images.
def raw152 : PartialTable := fun q b =>
  if q = 0 ∧ b = 0 then some ⟨1, .R, 1⟩
  else if q = 1 ∧ b = 0 then some ⟨1, .R, 3⟩
  else none

def raw156 : PartialTable := fun q b =>
  if q = 0 ∧ b = 0 then some ⟨1, .R, 1⟩
  else if q = 1 ∧ b = 0 then some ⟨1, .R, 4⟩
  else none

def raw160 : PartialTable := fun q b =>
  if q = 0 ∧ b = 0 then some ⟨1, .R, 1⟩
  else if q = 1 ∧ b = 0 then some ⟨1, .R, 5⟩
  else none

-- A transposition acts on both table rows and target states.
def swapState (i j q : State) : State :=
  if q = i then j else if q = j then i else q

def renameBySwap (i j : State) (e : PartialTable) : PartialTable := fun q b =>
  match e (swapState i j q) b with
  | none => none
  | some m => some { m with next := swapState i j m.next }

-- The three nontrivial images of C under the root-fixing S4 action.
def renameCD (e : PartialTable) : PartialTable := renameBySwap 2 3 e
def renameCE (e : PartialTable) : PartialTable := renameBySwap 2 4 e
def renameCF (e : PartialTable) : PartialTable := renameBySwap 2 5 e

-- Child refines parent iff it preserves every assigned parent transition.
def refines (child parent : PartialTable) : Prop :=
  ∀ q b, parent q b = none ∨ child q b = parent q b

def states : List State := List.ofFn (fun q : State => q)
def bits : List Bit := List.ofFn (fun b : Bit => b)

theorem mem_states (q : State) : q ∈ states := by
  rw [states, List.mem_ofFn]
  exact ⟨q, rfl⟩

theorem mem_bits (b : Bit) : b ∈ bits := by
  rw [bits, List.mem_ofFn]
  exact ⟨b, rfl⟩

def refinesB (child parent : PartialTable) : Bool :=
  states.all (fun q => bits.all (fun b =>
    match parent q b with
    | none => true
    | some tr => decide (child q b = some tr)))

theorem refinesB_sound {child parent : PartialTable}
    (h : refinesB child parent = true) : refines child parent := by
  intro q b
  unfold refinesB at h
  have hq := (List.all_eq_true.mp h) q (mem_states q)
  have hb := (List.all_eq_true.mp hq) b (mem_bits b)
  cases hp : parent q b with
  | none => left; rfl
  | some tr =>
    right
    have hdec : decide (child q b = some tr) = true := by simpa [hp] using hb
    exact of_decide_eq_true hdec

def tableEqB (x y : PartialTable) : Bool :=
  states.all (fun q => bits.all (fun b => decide (x q b = y q b)))

theorem tableEqB_sound {x y : PartialTable} (h : tableEqB x y = true) : x = y := by
  funext q b
  unfold tableEqB at h
  have hq := (List.all_eq_true.mp h) q (mem_states q)
  have hb := (List.all_eq_true.mp hq) b (mem_bits b)
  exact of_decide_eq_true hb

/-- The C<->D image of q32 is a strict refinement of raw152. -/
theorem q32_CD_image_is_raw152_refinement : refines (renameCD q32) raw152 := by
  apply refinesB_sound
  decide

theorem q32_CD_image_not_refining_raw152 : ¬ refines raw152 (renameCD q32) := by
  intro h
  have hD0 := h 3 0
  simp [renameCD, renameBySwap, q32, raw152, swapState] at hD0

theorem q32_CD_image_is_strict_refinement :
    refines (renameCD q32) raw152 ∧ ¬ refines raw152 (renameCD q32) := by
  exact ⟨q32_CD_image_is_raw152_refinement, q32_CD_image_not_refining_raw152⟩

theorem q32_CE_image_is_raw156_refinement : refines (renameCE q32) raw156 := by
  apply refinesB_sound
  decide

theorem q32_CE_image_not_refining_raw156 : ¬ refines raw156 (renameCE q32) := by
  intro h
  have hE0 := h 4 0
  simp [renameCE, renameBySwap, q32, raw156, swapState] at hE0

theorem q32_CF_image_is_raw160_refinement : refines (renameCF q32) raw160 := by
  apply refinesB_sound
  decide

theorem q32_CF_image_not_refining_raw160 : ¬ refines raw160 (renameCF q32) := by
  intro h
  have hF0 := h 5 0
  simp [renameCF, renameBySwap, q32, raw160, swapState] at hF0

theorem q32_CE_image_is_strict_refinement :
    refines (renameCE q32) raw156 ∧ ¬ refines raw156 (renameCE q32) := by
  exact ⟨q32_CE_image_is_raw156_refinement, q32_CE_image_not_refining_raw156⟩

theorem q32_CF_image_is_strict_refinement :
    refines (renameCF q32) raw160 ∧ ¬ refines raw160 (renameCF q32) := by
  exact ⟨q32_CF_image_is_raw160_refinement, q32_CF_image_not_refining_raw160⟩

theorem raw152_DE_image_eq_raw156 : renameBySwap 3 4 raw152 = raw156 := by
  apply tableEqB_sound
  decide

theorem raw152_DF_image_eq_raw160 : renameBySwap 3 5 raw152 = raw160 := by
  apply tableEqB_sound
  decide

#print axioms all_safe_of_orbit_cover
#print axioms q32_CD_image_is_strict_refinement
#print axioms q32_CE_image_is_strict_refinement
#print axioms q32_CF_image_is_strict_refinement
#print axioms raw152_DE_image_eq_raw156
#print axioms raw152_DF_image_eq_raw160
