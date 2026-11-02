import Symmetry
import Lean.Elab.Tactic.Omega
namespace BB6Coverage

variable (m : Machine) (b c : Fin 6) (u v z : Bool)

/-- A four-step rightward glider: on first entering a fresh-zero cell A,
    write 1 and explore the next zero via B, bounce left, read the marker,
    then step twice to the next fresh-zero A cell. -/
def FourGlider : Prop :=
  m (0,false) = some ⟨true,true,b⟩ ∧
  m (b,false) = some ⟨v,false,0⟩ ∧
  m (0,true) = some ⟨u,true,c⟩ ∧
  m (c,v) = some ⟨z,true,0⟩

private def Fresh (q : Config) : Prop :=
  q.state = 0 ∧ ∀ x, q.head ≤ x → q.tape x = false

private theorem fresh_cycle (q : Config) (h : FourGlider m b c u v z)
    (hq : Fresh q) :
    ∃ q', run m 4 q = some q' ∧ Fresh q' ∧ q'.head = q.head + 2 := by
  obtain ⟨ha,hb,hc,hd⟩ := h
  obtain ⟨hstate,hfresh⟩ := hq
  let q1 := applyMove q ⟨true,true,b⟩
  let q2 := applyMove q1 ⟨v,false,0⟩
  let q3 := applyMove q2 ⟨u,true,c⟩
  let q4 := applyMove q3 ⟨z,true,0⟩
  have h0 : q.tape q.head = false := hfresh _ (by omega)
  have h1 : q1.tape q1.head = false := by
    have hneq : q.head + 1 ≠ q.head := by omega
    simpa [q1,applyMove,hneq] using hfresh (q.head+1) (by omega)
  have hhead1 : q1.head = q.head + 1 := rfl
  have hhead2 : q2.head = q.head := by
    dsimp [q2,q1,applyMove]
    omega
  have hhead3 : q3.head = q.head + 1 := by
    dsimp [q3,q2,q1,applyMove]
    omega
  have hhead4 : q4.head = q.head + 2 := by
    dsimp [q4,q3,q2,q1,applyMove]
    omega
  have h2 : q2.tape q2.head = true := by
    change (if q2.head = q1.head then v else if q2.head = q.head then true else q.tape q2.head) = true
    rw [hhead2,hhead1]
    simp <;> omega
  have h3 : q3.tape q3.head = v := by
    change (if q3.head = q2.head then u else
      if q3.head = q1.head then v else if q3.head = q.head then true else q.tape q3.head) = v
    rw [hhead3,hhead2,hhead1]
    simp <;> omega
  have hr1 : rawStep m q = some q1 := by
    change (m (q.state, q.tape q.head)).map (applyMove q) = some q1
    rw [hstate,h0,ha]
    rfl
  have hr2 : rawStep m q1 = some q2 := by
    change (m (q1.state, q1.tape q1.head)).map (applyMove q1) = some q2
    rw [h1]
    change (m (b,false)).map (applyMove q1) = some q2
    rw [hb]
    rfl
  have hr3 : rawStep m q2 = some q3 := by
    change (m (q2.state, q2.tape q2.head)).map (applyMove q2) = some q3
    rw [h2]
    change (m (0,true)).map (applyMove q2) = some q3
    rw [hc]
    rfl
  have hr4 : rawStep m q3 = some q4 := by
    change (m (q3.state, q3.tape q3.head)).map (applyMove q3) = some q4
    rw [h3]
    change (m (c,v)).map (applyMove q3) = some q4
    rw [hd]
    rfl
  have ht : run m 4 q = some q4 := by
    simp [run, hr1, hr2, hr3, hr4]
  refine ⟨q4, ht, ?_, ?_⟩
  constructor
  · simp [q4,q3,applyMove]
  · intro x hx
    have hnew : q.head + 2 ≤ x := by
      rw [hhead4] at hx
      exact hx
    have hne1 : x ≠ q.head := by omega
    have hne2 : x ≠ q.head + 1 := by omega
    change (if x = q3.head then z else if x = q2.head then u else
      if x = q1.head then v else if x = q.head then true else q.tape x) = false
    rw [hhead3,hhead2,hhead1]
    simp [hne1,hne2,hfresh x (by omega)]
  · exact hhead4

private theorem run_add (m : Machine) (q : Config) (n k : Nat) :
    run m (n+k) q = (run m n q).bind (run m k) := by
  induction k with
  | zero => simp [run]
  | succ k ih =>
    rw [Nat.add_succ, run, ih]
    cases h : run m n q with
    | none => simp
    | some d => rfl

private theorem run_some_prefix (m : Machine) (q : Config) (N n : Nat)
    (hn : n≤N) (hN : (run m N q).isSome=true) :
    (run m n q).isSome=true := by
  rcases Nat.exists_eq_add_of_le hn with ⟨k,hk⟩
  cases h : run m n q with
  | some d => simp
  | none =>
    have hm : run m N q = none := by
      rw [hk,run_add, h]
      rfl
    simp [hm] at hN

private theorem fresh_four_multiples (h : FourGlider m b c u v z) (n : Nat) :
    ∃ q, run m (4*n) blank = some q ∧ Fresh q := by
  induction n with
  | zero =>
    refine ⟨blank, by rfl, ?_⟩
    constructor
    · rfl
    · intro x hx
      rfl
  | succ n ih =>
    obtain ⟨q,hq,hfresh⟩ := ih
    obtain ⟨q',hfour,hfresh',_⟩ := fresh_cycle m b c u v z q h hfresh
    refine ⟨q', ?_, hfresh'⟩
    have htime : 4*(n+1) = 4*n+4 := by omega
    rw [htime, run_add,hq]
    exact hfour

/-- Every fully specified glider of this form runs forever from blank. -/
theorem four_glider_never (h : FourGlider m b c u v z) : NeverHalts m := by
  intro n
  obtain ⟨q,hq,_⟩ := fresh_four_multiples m b c u v z h (n+1)
  apply run_some_prefix m blank (4*(n+1)) n (by omega)
  simp [hq]

/-- A locally checked sparse four-slot leaf. Other eight table entries are free. -/
def PartialFourGlider (p : PartialMachine) : Prop :=
  p (0,false) = some (some ⟨true,true,b⟩) ∧
  p (b,false) = some (some ⟨v,false,0⟩) ∧
  p (0,true) = some (some ⟨u,true,c⟩) ∧
  p (c,v) = some (some ⟨z,true,0⟩)

theorem partial_glider_cover (p : PartialMachine) (B : Nat)
    (hp : PartialFourGlider b c u v z p) : Cover (DecidedBelow B) p := by
  apply Cover.leaf
  intro m hm
  left
  apply four_glider_never m b c u v z
  obtain ⟨h0,h1,h2,h3⟩ := hp
  exact ⟨hm _ _ h0, hm _ _ h1, hm _ _ h2, hm _ _ h3⟩

def gliderExample : PartialMachine := fun s =>
  if s = (0,false) then some (some ⟨true,true,1⟩)
  else if s = (1,false) then some (some ⟨false,false,0⟩)
  else if s = (0,true) then some (some ⟨false,true,2⟩)
  else if s = (2,false) then some (some ⟨false,true,0⟩)
  else none

theorem example_glider_cover (B : Nat) : Cover (DecidedBelow B) gliderExample := by
  exact partial_glider_cover (b:=1) (c:=2) (u:=false) (v:=false) (z:=false)
    gliderExample B (by simp [PartialFourGlider, gliderExample])

#print axioms four_glider_never
#print axioms partial_glider_cover
#print axioms example_glider_cover

/-- Leftward reflected glider: a second certified nonhalting family. -/
def PartialLeftGlider (p : PartialMachine) : Prop :=
  p (0,false) = some (some ⟨true,false,b⟩) ∧
  p (b,false) = some (some ⟨v,true,0⟩) ∧
  p (0,true) = some (some ⟨u,false,c⟩) ∧
  p (c,v) = some (some ⟨z,false,0⟩)

private theorem mirror_never (m : Machine)
    (h : NeverHalts (reflectTable m)) : NeverHalts m := by
  intro n
  have hr := mirror_run m blank n
  simp only [mirror_blank] at hr
  cases ht : run m n blank with
  | none =>
    simp only [ht, Option.map_none] at hr
    have hn := h n
    rw [hr] at hn
    simp at hn
  | some q => simp

/-- Sparse mirror family, with complete infinite-tape reflection proof. -/
theorem partial_left_glider_cover (p : PartialMachine) (B : Nat)
    (hp : PartialLeftGlider b c u v z p) : Cover (DecidedBelow B) p := by
  apply Cover.leaf
  intro m hm
  left
  apply mirror_never m
  apply four_glider_never (reflectTable m) b c u v z
  obtain ⟨h0,h1,h2,h3⟩ := hp
  have h0' := hm _ _ h0
  have h1' := hm _ _ h1
  have h2' := hm _ _ h2
  have h3' := hm _ _ h3
  simp [FourGlider,reflectTable,reflectMove,h0',h1',h2',h3']

#print axioms partial_left_glider_cover


/-- Three-step backtracking glider: first paint the old frontier, then bounce back,
    finally depart toward the next completely blank frontier. -/
def ThreeGlider : Prop :=
  m (0,false) = some ⟨true,true,b⟩ ∧
  m (b,false) = some ⟨false,false,c⟩ ∧
  m (c,true) = some ⟨u,true,0⟩

private theorem three_cycle (q : Config) (h : ThreeGlider m b c u)
    (hq : Fresh q) :
    ∃ q', run m 3 q = some q' ∧ Fresh q' ∧ q'.head = q.head + 1 := by
  obtain ⟨ha,hb,hc⟩ := h
  obtain ⟨hstate,hfresh⟩ := hq
  let q1 := applyMove q ⟨true,true,b⟩
  let q2 := applyMove q1 ⟨false,false,c⟩
  let q3 := applyMove q2 ⟨u,true,0⟩
  have h0 : q.tape q.head = false := hfresh _ (by omega)
  have hhead1 : q1.head = q.head + 1 := rfl
  have hhead2 : q2.head = q.head := by
    dsimp [q2,q1,applyMove]
    omega
  have hhead3 : q3.head = q.head + 1 := by
    dsimp [q3,q2,q1,applyMove]
    omega
  have h1 : q1.tape q1.head = false := by
    have hneq : q.head + 1 ≠ q.head := by omega
    simpa [q1,applyMove,hneq] using hfresh (q.head+1) (by omega)
  have h2 : q2.tape q2.head = true := by
    change (if q2.head = q1.head then false else if q2.head = q.head then true else q.tape q2.head) = true
    rw [hhead2,hhead1]
    simp <;> omega
  have hr1 : rawStep m q = some q1 := by
    change (m (q.state, q.tape q.head)).map (applyMove q) = some q1
    rw [hstate,h0,ha]
    rfl
  have hr2 : rawStep m q1 = some q2 := by
    change (m (q1.state, q1.tape q1.head)).map (applyMove q1) = some q2
    rw [h1]
    change (m (b,false)).map (applyMove q1) = some q2
    rw [hb]
    rfl
  have hr3 : rawStep m q2 = some q3 := by
    change (m (q2.state, q2.tape q2.head)).map (applyMove q2) = some q3
    rw [h2]
    change (m (c,true)).map (applyMove q2) = some q3
    rw [hc]
    rfl
  have ht : run m 3 q = some q3 := by
    simp [run,hr1,hr2,hr3]
  refine ⟨q3, ht, ?_, ?_⟩
  constructor
  · simp [q3,applyMove]
  · intro x hx
    have hne1 : x ≠ q.head := by
      rw [hhead3] at hx
      omega
    change (if x = q2.head then u else if x = q1.head then false else
      if x = q.head then true else q.tape x) = false
    rw [hhead2,hhead1]
    simp [hne1,hfresh x (by rw [hhead3] at hx; omega)]
  · exact hhead3

private theorem fresh_three_multiples (h : ThreeGlider m b c u) (n : Nat) :
    ∃ q, run m (3*n) blank = some q ∧ Fresh q := by
  induction n with
  | zero =>
    refine ⟨blank, by rfl, ?_⟩
    constructor
    · rfl
    · intro x hx
      rfl
  | succ n ih =>
    obtain ⟨q,hq,hfresh⟩ := ih
    obtain ⟨q',hthree,hfresh',_⟩ := three_cycle m b c u q h hfresh
    refine ⟨q', ?_, hfresh'⟩
    have htime : 3*(n+1) = 3*n+3 := by omega
    rw [htime,run_add,hq]
    exact hthree

/-- A genuine three-move macro recurs on virgin blanks forever. -/
theorem three_glider_never (h : ThreeGlider m b c u) : NeverHalts m := by
  intro n
  obtain ⟨q,hq,_⟩ := fresh_three_multiples m b c u h (n+1)
  apply run_some_prefix m blank (3*(n+1)) n (by omega)
  simp [hq]

/-- Three ordinary transitions determine an all-time nonhalting leaf. -/
def PartialThreeGlider (p : PartialMachine) : Prop :=
  p (0,false) = some (some ⟨true,true,b⟩) ∧
  p (b,false) = some (some ⟨false,false,c⟩) ∧
  p (c,true) = some (some ⟨u,true,0⟩)

theorem partial_three_glider_cover (p : PartialMachine) (B : Nat)
    (hp : PartialThreeGlider b c u p) : Cover (DecidedBelow B) p := by
  apply Cover.leaf
  intro m hm
  left
  apply three_glider_never m b c u
  obtain ⟨h0,h1,h2⟩ := hp
  exact ⟨hm _ _ h0,hm _ _ h1,hm _ _ h2⟩

/-- The mirror moves left forever, with one reversal per period. -/
def PartialLeftThreeGlider (p : PartialMachine) : Prop :=
  p (0,false) = some (some ⟨true,false,b⟩) ∧
  p (b,false) = some (some ⟨false,true,c⟩) ∧
  p (c,true) = some (some ⟨u,false,0⟩)

theorem partial_left_three_glider_cover (p : PartialMachine) (B : Nat)
    (hp : PartialLeftThreeGlider b c u p) : Cover (DecidedBelow B) p := by
  apply Cover.leaf
  intro m hm
  left
  apply mirror_never m
  apply three_glider_never (reflectTable m) b c u
  obtain ⟨h0,h1,h2⟩ := hp
  have h0' := hm _ _ h0
  have h1' := hm _ _ h1
  have h2' := hm _ _ h2
  simp [ThreeGlider,reflectTable,reflectMove,h0',h1',h2']

def threeGliderExample : PartialMachine := fun s =>
  if s = (0,false) then some (some ⟨true,true,1⟩)
  else if s = (1,false) then some (some ⟨false,false,2⟩)
  else if s = (2,true) then some (some ⟨false,true,0⟩)
  else none

theorem three_glider_example_cover (B : Nat) :
    Cover (DecidedBelow B) threeGliderExample := by
  exact partial_three_glider_cover (b:=1) (c:=2) (u:=false)
    threeGliderExample B (by simp [PartialThreeGlider,threeGliderExample])

#print axioms three_glider_never
#print axioms partial_three_glider_cover
#print axioms partial_left_three_glider_cover
#print axioms three_glider_example_cover


/-- A degenerate four-step glider uses only three distinct transition slots. -/
def fourDegenerateExample : PartialMachine := fun s =>
  if s = (0,false) then some (some ⟨true,true,1⟩)
  else if s = (1,false) then some (some ⟨true,false,0⟩)
  else if s = (0,true) then some (some ⟨false,true,0⟩)
  else none

theorem four_degenerate_example_cover (B : Nat) :
    Cover (DecidedBelow B) fourDegenerateExample := by
  exact partial_glider_cover (b:=1) (c:=0) (u:=false) (v:=true) (z:=false)
    fourDegenerateExample B (by simp [PartialFourGlider,fourDegenerateExample])

#print axioms four_degenerate_example_cover

end BB6Coverage
