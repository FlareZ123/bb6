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

/-- Any successful monitored run bounds both its initial and final head
    by the reported maximum. -/
theorem runWithHeadMax_head_bound (m : Machine) :
    ∀ (n : Nat) (c d : Config) (h : Int),
      runWithHeadMax m n c = some (d, h) → c.head ≤ h ∧ d.head ≤ h := by
  intro n
  induction n with
  | zero =>
      intro c d h hh
      simp only [runWithHeadMax, Option.some.injEq, Prod.mk.injEq] at hh
      rcases hh with ⟨rfl, rfl⟩
      exact ⟨Int.le_refl _, Int.le_refl _⟩
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
              have hprev := ih c p hm (by simp [hp])
              rcases hprev with ⟨hc, hphead⟩
              have hmax : max hm q.head = h := congrArg Prod.snd hpair
              constructor
              · calc
                  c.head ≤ hm := hc
                  _ ≤ max hm q.head := Int.le_max_left _ _
                  _ = h := hmax
              · have hd : q = d := congrArg Prod.fst hpair
                subst d
                calc
                  q.head ≤ max hm q.head := Int.le_max_right _ _
                  _ = h := hmax

/-- Segment composition for the head-maximum monitor. The maximum over
    a concatenated run is the maximum of the two segment maxima. -/
theorem runWithHeadMax_add (m : Machine) (n k : Nat) (c : Config) :
    runWithHeadMax m (n + k) c =
      (runWithHeadMax m n c).bind (fun (d, h₁) =>
        (runWithHeadMax m k d).map (fun (e, h₂) => (e, max h₁ h₂))) := by
  induction k with
  | zero =>
      simp only [Nat.add_zero]
      cases h : runWithHeadMax m n c with
      | none => simp
      | some p =>
          rcases p with ⟨d, hm⟩
          have hhead := (runWithHeadMax_head_bound m n c d hm h).2
          simp [runWithHeadMax, Int.max_eq_left hhead]
  | succ k ih =>
      change (runWithHeadMax m (n + k) c).bind (fun (d, h₁) =>
        (rawStep m d).map (fun e => (e, max h₁ e.head))) =
        (runWithHeadMax m n c).bind (fun (d, h₁) =>
          (runWithHeadMax m (k + 1) d).map (fun (e, h₂) => (e, max h₁ h₂)))
      rw [ih]
      simp [Option.bind_assoc, Option.map_bind, Option.bind_map]
      congr 1
      funext y
      congr 1
      funext z
      simp [Function.comp_def, Int.max_assoc]

/-- Exact two-step law for the head-maximum monitor, stated in terms of
    the two primitive raw transitions. -/
theorem runWithHeadMax_two_of_rawSteps (m : Machine) (c c₁ c₂ : Config)
    (h₁ : rawStep m c = some c₁) (h₂ : rawStep m c₁ = some c₂) :
    runWithHeadMax m 2 c =
      some (c₂, max (max c.head c₁.head) c₂.head) := by
  simp [runWithHeadMax, h₁, h₂, Int.max_assoc]

/-- A raw step changes no tape cell other than its scanned cell. -/
theorem rawStep_tape_eq_of_ne (m : Machine) (c d : Config)
    (hstep : rawStep m c = some d) (x : Int) (hx : x ≠ c.head) :
    d.tape x = c.tape x := by
  cases hm : m (readSlot c) with
  | none => simp [rawStep, hm] at hstep
  | some mv =>
      have heq : d = applyMove c mv := by
        exact (Option.some.inj (by simpa [rawStep, hm] using hstep)).symm
      subst d
      simp [applyMove, hx]

/-- No cell strictly beyond a successful run's maximum head can have been
    written during that run; its tape value is unchanged. -/
theorem runWithHeadMax_tape_above (m : Machine) :
    ∀ (n : Nat) (c d : Config) (h : Int),
      runWithHeadMax m n c = some (d, h) →
      ∀ x : Int, h < x → d.tape x = c.tape x := by
  intro n
  induction n with
  | zero =>
      intro c d h hh x hx
      simp only [runWithHeadMax, Option.some.injEq, Prod.mk.injEq] at hh
      rcases hh with ⟨rfl, rfl⟩
      rfl
  | succ n ih =>
      intro c d h hh x hx
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
              have hmax : max hm q.head = h := congrArg Prod.snd hpair
              have hmle : hm ≤ h := by
                rw [← hmax]
                exact Int.le_max_left _ _
              have hprev := ih c p hm (by simp [hp]) x (Int.lt_of_le_of_lt hmle hx)
              have hhead : p.head ≤ hm :=
                (runWithHeadMax_head_bound m n c p hm (by simp [hp])).2
              have hstepTape := rawStep_tape_eq_of_ne m p q hs x (by omega)
              have hd : q = d := congrArg Prod.fst hpair
              subst d
              rw [hstepTape, hprev]

/-- If a monitored endpoint is at the reported maximum, its right neighbor
    is untouched by the run. If the input tape is blank to the right of F
    and F is no farther right than that maximum, the neighbor is blank. -/
theorem runWithHeadMax_current_max_right_blank (m : Machine)
    (n : Nat) (c d : Config) (M F : Int)
    (hmon : runWithHeadMax m n c = some (d, M))
    (hhead : d.head = M) (hF : F ≤ M)
    (hblank : ∀ x, F < x → c.tape x = false) :
    d.tape (d.head + 1) = false := by
  have hunchanged := runWithHeadMax_tape_above m n c d M hmon
    (M + 1) (by omega)
  rw [hhead, hunchanged]
  exact hblank (M + 1) (by omega)

/-- Intermediate D/0 configuration reached by a C/0 gate. -/
def c0GateMid (c : Config) : Config :=
  { state := (3 : Fin 6)
    head := c.head + 1
    tape := writeAt c.tape c.head false }

/-- Exact two-step continuation of a safe C/0 gate: C/0 writes 0 and
    moves right to D/0, then D/0 writes 1 and returns left to E/1. -/
def c0GateAfterTwo (c : Config) : Config :=
  { state := (4 : Fin 6)
    head := c.head
    tape := writeAt (writeAt c.tape c.head false) (c.head + 1) true }

theorem source429_c0_gate_raw_steps (c : Config)
    (hstate : c.state = (2 : Fin 6))
    (hread : c.tape c.head = false)
    (hright : c.tape (c.head + 1) = false) :
    rawStep source429 c = some (c0GateMid c) ∧
      rawStep source429 (c0GateMid c) = some (c0GateAfterTwo c) := by
  have hfirst : rawStep source429 c = some (c0GateMid c) := by
    simp [c0GateMid, rawStep, source429, move, applyMove, hstate, hread]
    funext x
    by_cases hx : x = c.head <;> simp [writeAt, hx]
  have hslot1 : readSlot (c0GateMid c) = ((3 : Fin 6), false) := by
    simp [readSlot, c0GateMid, writeAt, hright]
  have hlookup1 : source429 (readSlot (c0GateMid c)) = move true false 4 := by
    rw [hslot1]
    rfl
  have hsecond : rawStep source429 (c0GateMid c) = some (c0GateAfterTwo c) := by
    change (source429 (readSlot (c0GateMid c))).map
      (applyMove (c0GateMid c)) = _
    rw [hlookup1]
    simp only [move, Option.map_some]
    apply congrArg some
    have hhead : c.head + 1 + -1 = c.head := by omega
    simp [c0GateMid, c0GateAfterTwo, applyMove, writeAt, hhead]
    funext x
    by_cases h1 : x = c.head + 1
    · subst x
      simp [writeAt]
    · by_cases h2 : x = c.head
      · subst x
        simp [writeAt, h1]
      · simp [writeAt, h1, h2]
  exact ⟨hfirst, hsecond⟩

theorem source429_c0_gate_two_steps (c : Config)
    (hstate : c.state = (2 : Fin 6))
    (hread : c.tape c.head = false)
    (hright : c.tape (c.head + 1) = false) :
    run source429 2 c = some (c0GateAfterTwo c) := by
  obtain ⟨hfirst, hsecond⟩ :=
    source429_c0_gate_raw_steps c hstate hread hright
  simp [run, hfirst, hsecond]

/-- A safe C/0 gate's two-step monitor has maximum exactly one cell
    to the right of its input head. -/
theorem source429_c0_gate_monitor (c : Config)
    (hstate : c.state = (2 : Fin 6))
    (hread : c.tape c.head = false)
    (hright : c.tape (c.head + 1) = false) :
    runWithHeadMax source429 2 c = some (c0GateAfterTwo c, c.head + 1) := by
  obtain ⟨hfirst, hsecond⟩ :=
    source429_c0_gate_raw_steps c hstate hread hright
  have hmid : (c0GateMid c).head = c.head + 1 := by
    rfl
  have hend : (c0GateAfterTwo c).head = c.head := by
    rfl
  have hmax : max (max c.head (c0GateMid c).head) (c0GateAfterTwo c).head =
      c.head + 1 := by
    rw [hmid, hend]
    have hinner : max c.head (c.head + 1) = c.head + 1 :=
      Int.max_eq_right (by omega)
    rw [hinner]
    exact Int.max_eq_left (by omega)
  simpa [hmax] using
    (runWithHeadMax_two_of_rawSteps source429 c (c0GateMid c)
      (c0GateAfterTwo c) hfirst hsecond)

/-- The C/0-to-E/1 two-step gate writes the new rightmost mark one cell
    beyond its input head whenever the old tape had a right blank tail. -/
theorem c0GateAfterTwo_frontier (c : Config) (F : Int)
    (hF : F ≤ c.head)
    (hblank : ∀ x, F < x → c.tape x = false) :
    (c0GateAfterTwo c).tape (c.head + 1) = true ∧
    (∀ x, c.head + 1 < x → (c0GateAfterTwo c).tape x = false) := by
  constructor
  · simp [c0GateAfterTwo, writeAt]
  · intro x hx
    have h1 : x ≠ c.head + 1 := by omega
    have h2 : x ≠ c.head := by omega
    simp [c0GateAfterTwo, writeAt, h1, h2]
    exact hblank x (by omega)

/-- A C/0 event at the monitored head maximum is safe and advances the
    rightmost mark by one, provided the input tape had a blank right tail
    beginning no farther right than that maximum. -/
theorem source429_c0_gate_advance_of_record
    (n : Nat) (c d : Config) (M F : Int)
    (hmon : runWithHeadMax source429 n c = some (d, M))
    (hhead : d.head = M) (hF : F ≤ M)
    (hblank : ∀ x, F < x → c.tape x = false)
    (hstate : d.state = (2 : Fin 6))
    (hread : d.tape d.head = false) :
    run source429 2 d = some (c0GateAfterTwo d) ∧
    (c0GateAfterTwo d).tape (M + 1) = true ∧
    (∀ x, M + 1 < x → (c0GateAfterTwo d).tape x = false) := by
  have hright := runWithHeadMax_current_max_right_blank
    source429 n c d M F hmon hhead hF hblank
  have hrun := source429_c0_gate_two_steps d hstate hread hright
  have hblankD : ∀ x, M < x → d.tape x = false := by
    intro x hx
    rw [runWithHeadMax_tape_above source429 n c d M hmon x hx]
    exact hblank x (by omega)
  have hfront := c0GateAfterTwo_frontier d M
    (by rw [hhead]; omega) hblankD
  refine ⟨hrun, ?_, ?_⟩
  · simpa [hhead] using hfront.1
  · intro x hx
    have hx' : d.head + 1 < x := by rw [hhead]; exact hx
    simpa [hhead] using hfront.2 x hx'

/-- The same 35-step root trace never visits a head coordinate above 6. -/
theorem blank_reaches_j00_with_head_max :
    runWithHeadMax source429 35 blank = some (j00Config, 6) := by
  rfl

/-- The raw physical configuration and cumulative head maximum after the
    source-table 110-step continuation from J(0,0). -/
def rootAfterHigh0 : Config × Int :=
  (runWithHeadMax source429 110 j00Config).getD (j00Config, 3)

theorem root_high0_monitor_computes :
    runWithHeadMax source429 110 j00Config = some rootAfterHigh0 := by
  rfl

theorem root_high0_head_max : rootAfterHigh0.2 = 12 := by
  decide

theorem root_high0_head_endpoint : rootAfterHigh0.1.head = -3 := by
  decide

theorem root_high0_tape_at_12 : rootAfterHigh0.1.tape 12 = true := by
  decide

theorem root_high0_tape_blank_right (x : Int) (hx : 12 < x) :
    rootAfterHigh0.1.tape x = false := by
  rw [runWithHeadMax_tape_above source429 110 j00Config rootAfterHigh0.1 12
    root_high0_monitor_computes x hx]
  exact rootTape_blank_right_of_six x (by omega)

/-- The high-zero raw prefix advances the physical frontier from 6 to 12,
    and its maximum visited head is exactly the new rightmost mark. -/
theorem root_high0_frontier_base :
    rootAfterHigh0.2 = 12 ∧ rootAfterHigh0.1.tape 12 = true ∧
    (∀ x, 12 < x → rootAfterHigh0.1.tape x = false) := by
  exact ⟨root_high0_head_max, root_high0_tape_at_12,
    fun x hx => root_high0_tape_blank_right x hx⟩

/-- Concrete root prefix at the end of the first high0/Junc cycle. -/
def rootAfter271 : Config × Int :=
  (runWithHeadMax source429 271 blank).getD (blank, 0)

theorem root_after_271_computes :
    runWithHeadMax source429 271 blank = some rootAfter271 := by
  rfl

theorem root_after_271_head_max : rootAfter271.2 = 12 := by
  decide

theorem root_after_271_head : rootAfter271.1.head = 11 := by
  decide

theorem root_after_271_rightmost_mark : rootAfter271.1.tape 12 = true := by
  decide

theorem root_after_271_blank_right (x : Int) (hx : 12 < x) :
    rootAfter271.1.tape x = false := by
  rw [runWithHeadMax_tape_above source429 271 blank rootAfter271.1 12
    root_after_271_computes x hx]
  rfl

/-- The fifth C/0 gate of the blank-root run is reached at the current
    head maximum, with a blank cell immediately to its right. -/
def rootAt275 : Config × Int :=
  (runWithHeadMax source429 275 blank).getD (blank, 0)

theorem root_at_275_computes :
    runWithHeadMax source429 275 blank = some rootAt275 := by
  rfl

theorem root_at_275_state : rootAt275.1.state = (2 : Fin 6) := by
  decide

theorem root_at_275_head : rootAt275.1.head = 15 := by
  decide

theorem root_at_275_max : rootAt275.2 = 15 := by
  decide

theorem root_at_275_reads_zero : rootAt275.1.tape 15 = false := by
  decide

theorem root_at_275_right_blank : rootAt275.1.tape 16 = false := by
  rw [runWithHeadMax_tape_above source429 275 blank rootAt275.1 15
    root_at_275_computes 16 (by omega)]
  rfl

/-- The fifth root C/0 event is safe by the generic current-maximum lemma,
    not by a direct lookup of its right-hand tape cell. -/
theorem root_at_275_safe_gate : rootAt275.1.tape (rootAt275.1.head + 1) = false := by
  apply runWithHeadMax_current_max_right_blank source429 275 blank rootAt275.1
    15 0 root_at_275_computes root_at_275_head (by omega)
  intro x hx
  simp [blank]

theorem root_at_275_gate_advance :
    run source429 2 rootAt275.1 = some (c0GateAfterTwo rootAt275.1) ∧
    (c0GateAfterTwo rootAt275.1).tape 16 = true ∧
    (∀ x, 16 < x → (c0GateAfterTwo rootAt275.1).tape x = false) := by
  exact source429_c0_gate_advance_of_record 275 blank rootAt275.1 15 0
    root_at_275_computes root_at_275_head (by omega)
    (by intro x hx; simp [blank]) root_at_275_state root_at_275_reads_zero

theorem root_at_275_gate_two_steps :
    run source429 2 rootAt275.1 = some (c0GateAfterTwo rootAt275.1) :=
  root_at_275_gate_advance.1

theorem root_at_275_gate_frontier :
    (c0GateAfterTwo rootAt275.1).tape 16 = true ∧
    (∀ x, 16 < x → (c0GateAfterTwo rootAt275.1).tape x = false) :=
  ⟨root_at_275_gate_advance.2.1, root_at_275_gate_advance.2.2⟩

/-- The C/0-to-D/0 continuation writes the new frontier cell at 16; after
    277 root steps the global head maximum and rightmost mark both equal 16. -/
def rootAfter277 : Config × Int :=
  (runWithHeadMax source429 277 blank).getD (blank, 0)

theorem root_after_277_computes :
    runWithHeadMax source429 277 blank = some rootAfter277 := by
  rfl

theorem root_after_277_monitor_exact :
    runWithHeadMax source429 277 blank =
      some (c0GateAfterTwo rootAt275.1, 16) := by
  have hgate := source429_c0_gate_monitor rootAt275.1 root_at_275_state
    root_at_275_reads_zero root_at_275_safe_gate
  have hcomp := runWithHeadMax_add source429 275 2 blank
  simp [root_at_275_computes, hgate] at hcomp
  rw [root_at_275_max, root_at_275_head] at hcomp
  have hmax : max (15 : Int) (15 + 1) = 16 := by
    rw [Int.max_eq_right (by omega)]
    omega
  rw [hmax] at hcomp
  exact hcomp

theorem root_after_277_pair :
    rootAfter277 = (c0GateAfterTwo rootAt275.1, 16) := by
  have hEq : some rootAfter277 =
      some (c0GateAfterTwo rootAt275.1, 16) := by
    rw [← root_after_277_computes]
    exact root_after_277_monitor_exact
  exact Option.some.inj hEq

theorem root_after_277_is_gate_endpoint :
    rootAfter277.1 = c0GateAfterTwo rootAt275.1 := by
  exact congrArg Prod.fst root_after_277_pair

theorem root_after_277_head_max : rootAfter277.2 = 16 := by
  rw [root_after_277_pair]

theorem root_after_277_head : rootAfter277.1.head = 15 := by
  rw [root_after_277_pair]
  exact root_at_275_head

theorem root_after_277_state : rootAfter277.1.state = (4 : Fin 6) := by
  rw [root_after_277_pair]
  rfl

theorem root_after_277_mark : rootAfter277.1.tape 16 = true := by
  rw [root_after_277_pair]
  simpa [root_at_275_head] using root_at_275_gate_frontier.1

theorem root_after_277_blank_right (x : Int) (hx : 16 < x) :
    rootAfter277.1.tape x = false := by
  rw [root_after_277_pair]
  have hx' : rootAt275.1.head + 1 < x := by rw [root_at_275_head]; exact hx
  simpa using root_at_275_gate_frontier.2 x hx'

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

#print axioms root_high0_monitor_computes
#print axioms root_high0_head_max
#print axioms root_high0_head_endpoint
#print axioms root_high0_tape_at_12
#print axioms root_high0_tape_blank_right
#print axioms root_high0_frontier_base
#print axioms runWithHeadMax_head_bound
#print axioms runWithHeadMax_current_max_right_blank
#print axioms source429_c0_gate_raw_steps
#print axioms source429_c0_gate_two_steps
#print axioms source429_c0_gate_monitor
#print axioms runWithHeadMax_two_of_rawSteps
#print axioms runWithHeadMax_add
#print axioms c0GateAfterTwo_frontier
#print axioms source429_c0_gate_advance_of_record
#print axioms rawStep_tape_eq_of_ne
#print axioms runWithHeadMax_tape_above
#print axioms root_after_271_computes
#print axioms root_after_271_head_max
#print axioms root_after_271_rightmost_mark
#print axioms root_after_271_blank_right
#print axioms root_at_275_computes
#print axioms root_at_275_right_blank
#print axioms root_at_275_safe_gate
#print axioms root_at_275_gate_advance
#print axioms root_at_275_gate_two_steps
#print axioms root_at_275_gate_frontier
#print axioms root_after_277_computes
#print axioms root_after_277_monitor_exact
#print axioms root_after_277_pair
#print axioms root_after_277_mark
#print axioms root_after_277_blank_right
#print axioms blank_reaches_j00_after_35
#print axioms runWithHeadMax_projects
#print axioms blank_reaches_j00_with_head_max
#print axioms rootTape_exact_support
#print axioms rootTape_matches_j00_shape
#print axioms rootTape_at_six
#print axioms rootTape_blank_right_of_six
#print axioms blank_root_frontier_base

end BB429RootEntry
