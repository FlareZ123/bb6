import Frontier

namespace BB429RootEntry

open BB6Coverage

/-- A concrete move in the original six-state #429 table. -/
def move (w r : Bool) (q : Fin 6) : Transition :=
  some ⟨w, r, q⟩

/-- The complete original #429 table, including the genuine D/1 halt.
    The wildcard is unreachable for a Fin 6 state; it makes the total
    function's pattern match exhaustive rather than introducing sorryAx. -/
def source429 : Machine := fun s =>
  match s.1.val, s.2 with
  | 0, false => move true true 1
  | 0, true  => move false false 5
  | 1, false => move true true 2
  | 1, true  => move true true 0
  | 2, false => move false true 3
  | 2, true  => move false true 1
  | 3, false => move true false 4
  | 3, true  => none
  | 4, false => move false false 0
  | 4, true  => move true false 4
  | 5, false => move true true 3
  | 5, true  => move true false 0
  | _, _ => none

/-- A primitive tape write, in the same convention as rawStep. -/
def writeAt (tape : Int → Bool) (p : Int) (b : Bool) : Int → Bool :=
  fun x => if x = p then b else tape x

/-- The complete ordered write trace of the 35-step blank-root prefix. -/
def rootWrites : List (Int × Bool) :=
  [ (0,true), (1,true), (2,false), (3,true), (2,false),
    (1,false), (0,true), (-1,true), (0,true), (1,true),
    (2,true), (3,false), (4,true), (5,false), (6,true),
    (5,false), (4,false), (3,true), (4,true), (3,true),
    (2,true), (1,true), (0,true), (-1,true), (-2,false),
    (-3,true), (-2,true), (-1,false), (0,true), (1,false),
    (0,true), (-1,true), (0,true), (1,true), (2,true) ]

/-- Finite-support tape obtained by applying the ordered raw writes to blank. -/
def rootTape : Int → Bool :=
  rootWrites.foldl (fun t wb => writeAt t wb.1 wb.2) (fun _ => false)

/-- Exact absolute-coordinate support of the endpoint tape. -/
theorem rootTape_exact_support (x : Int) :
    rootTape x = (if (-3 ≤ x ∧ x ≤ 4) ∨ x = 6 then true else false) := by
  by_cases h : -3 ≤ x ∧ x ≤ 6
  · have hx : x = -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨
        x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 := by omega
    rcases hx with h | h | h | h | h | h | h | h | h | h <;> subst x <;> decide
  · have hx : x < -3 ∨ 6 < x := by omega
    rcases hx with hx | hx
    · have h0 : x ≠ 0 := by omega
      have h1 : x ≠ 1 := by omega
      have h2 : x ≠ 2 := by omega
      have h3 : x ≠ 3 := by omega
      have h4 : x ≠ 4 := by omega
      have h5 : x ≠ 5 := by omega
      have h6 : x ≠ 6 := by omega
      have hm1 : x ≠ -1 := by omega
      have hm2 : x ≠ -2 := by omega
      have hm3 : x ≠ -3 := by omega
      simp [rootTape, rootWrites, writeAt, h0, h1, h2, h3, h4, h5, h6, hm1, hm2, hm3]
      omega
    · have h0 : x ≠ 0 := by omega
      have h1 : x ≠ 1 := by omega
      have h2 : x ≠ 2 := by omega
      have h3 : x ≠ 3 := by omega
      have h4 : x ≠ 4 := by omega
      have h5 : x ≠ 5 := by omega
      have h6 : x ≠ 6 := by omega
      have hm1 : x ≠ -1 := by omega
      have hm2 : x ≠ -2 := by omega
      have hm3 : x ≠ -3 := by omega
      simp [rootTape, rootWrites, writeAt, h0, h1, h2, h3, h4, h5, h6, hm1, hm2, hm3]
      omega

/-- J(0,0)'s relative tape predicate, written without importing the
    larger physical-prefix development. -/
def j00RelativeTape (r : Int) : Bool :=
  if (-6 ≤ r ∧ r ≤ 1) ∨ r = 3 then true else false

/-- The raw endpoint tape is exactly the J(0,0) pattern translated to
    absolute head coordinate 3. -/
theorem rootTape_matches_j00_shape (x : Int) :
    rootTape x = j00RelativeTape (x - 3) := by
  rw [rootTape_exact_support]
  have hcond : ((-3 ≤ x ∧ x ≤ 4) ∨ x = 6) ↔
      ((-6 ≤ x - 3 ∧ x - 3 ≤ 1) ∨ x - 3 = 3) := by omega
  simp [j00RelativeTape, hcond]

/-- The final J(0,0) tape has a mark at coordinate 6. -/
theorem rootTape_at_six : rootTape 6 = true := by
  rfl

/-- No cell strictly to the right of coordinate 6 is marked. -/
theorem rootTape_blank_right_of_six (x : Int) (hx : 6 < x) :
    rootTape x = false := by
  rw [rootTape_exact_support]
  simp
  omega

/-- The canonical J(0,0) endpoint, with head at absolute coordinate 3. -/
def j00Config : Config :=
  { state := 0
    head := 3
    tape := rootTape }

/-- Raw physical run monitor retaining the maximum head coordinate,
    including the initial and final configurations. -/
def runWithHeadMax (m : Machine) : Nat → Config → Option (Config × Int)
  | 0, c => some (c, c.head)
  | n+1, c =>
      (runWithHeadMax m n c).bind fun (d, h) =>
        (rawStep m d).map fun e => (e, max h e.head)

/-- The head-maximum monitor projects to the repository's raw run
    semantics: it changes no transition or halt convention. -/
theorem runWithHeadMax_projects (m : Machine) :
    ∀ (n : Nat) (c d : Config) (h : Int),
      runWithHeadMax m n c = some (d, h) → run m n c = some d := by
  intro n
  induction n with
  | zero =>
      intro c d h hh
      simpa [runWithHeadMax, run] using congrArg Prod.fst (Option.some.inj hh)
  | succ n ih =>
      intro c d h hh
      simp only [runWithHeadMax] at hh
      cases hp : runWithHeadMax m n c with
      | none => simp [hp] at hh
      | some p =>
          rcases p with ⟨p, hm⟩
          cases hs : rawStep m p with
          | none => simp [hp, hs] at hh
          | some q =>
              have hpair : (q, max hm q.head) = (d, h) := by
                simpa [hp, hs] using hh
              have hd : q = d := congrArg Prod.fst hpair
              have hprev := ih c p hm (by simp [hp])
              subst d
              simp [run, hprev, hs]

/-- The same 35-step root trace never visits a head coordinate above 6. -/
theorem blank_reaches_j00_with_head_max :
    runWithHeadMax source429 35 blank = some (j00Config, 6) := by
  rfl

/-- Candidate exact raw root entry: blank A reaches the physical J(0,0)
    tape after 35 primitive transitions. The manual CI workflow checks it. -/
theorem blank_reaches_j00_after_35 :
    run source429 35 blank = some j00Config := by
  exact runWithHeadMax_projects source429 35 blank j00Config 6
    blank_reaches_j00_with_head_max

/-- The root prefix establishes the induction base: its maximum head
    coordinate is exactly the endpoint tape's rightmost marked cell. -/
theorem blank_root_frontier_base :
    runWithHeadMax source429 35 blank = some (j00Config, 6) ∧
    rootTape 6 = true ∧ (∀ x, 6 < x → rootTape x = false) := by
  exact ⟨blank_reaches_j00_with_head_max, rootTape_at_six,
    fun x hx => rootTape_blank_right_of_six x hx⟩

#print axioms blank_reaches_j00_after_35
#print axioms runWithHeadMax_projects
#print axioms blank_reaches_j00_with_head_max
#print axioms rootTape_exact_support
#print axioms rootTape_matches_j00_shape
#print axioms rootTape_at_six
#print axioms rootTape_blank_right_of_six
#print axioms blank_root_frontier_base

end BB429RootEntry
