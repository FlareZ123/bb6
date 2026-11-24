import Lean

namespace BB6.Agent48Queue

/--
Potential-relevant projection of the pinned BusyCoq `verify/Enumerate62.v`
queue.  A node retains only `num_undef_trans` (holes) and
`min_unused_state` (cut); the transition table and decider payload are
deliberately erased.  The projection keeps the exact expansion multiplicities:
4m existing-state children and, when m<6, four least-fresh-state children.
Every child has one fewer hole.  This file proves the MAXT fuel bound only;
it does not prove decider soundness, queue coverage, or the holdout partition.
-/

structure Node where
  holes : Nat
  holes_pos : 1 ≤ holes
  cut : Fin 7

def weight (x : Node) : Nat := 25 ^ x.holes

def mass : List Node → Nat
  | [] => 0
  | x :: xs => weight x + mass xs

theorem weight_pos (x : Node) : 0 < weight x := by
  simp [weight]

theorem mass_append (xs ys : List Node) :
    mass (xs ++ ys) = mass xs + mass ys := by
  induction xs with
  | nil => simp [mass]
  | cons x xs ih => simp [mass, ih, Nat.add_assoc]

theorem mass_replicate (n : Nat) (x : Node) :
    mass (List.replicate n x) = n * weight x := by
  induction n with
  | zero => simp [mass]
  | succ n ih =>
      simp [mass, ih, Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

def existingChild (x : Node) (h : 2 ≤ x.holes) : Node :=
  { holes := x.holes - 1, holes_pos := by omega, cut := x.cut }

def freshChild (x : Node) (h : 2 ≤ x.holes)
    (hc : x.cut.val < 6) : Node :=
  { holes := x.holes - 1
    holes_pos := by omega
    cut := ⟨x.cut.val + 1, by omega⟩ }

/-- Exact `(holes,cut)` projection of the source's `expand`. -/
def expandProjection (x : Node) (h : 2 ≤ x.holes) : List Node :=
  List.replicate (4 * x.cut.val) (existingChild x h) ++
    (if hc : x.cut.val < 6 then
      List.replicate 4 (freshChild x h hc)
    else [])

/-- Source `expand'`: when one undefined transition remains, there are no
ordinary children; otherwise use the source expansion. -/
def expandProjection' (x : Node) : List Node :=
  if h : x.holes = 1 then [] else
    expandProjection x (by
      have hp : 1 ≤ x.holes := x.holes_pos
      omega)

theorem expandProjection_length (x : Node) (h : 2 ≤ x.holes) :
    (expandProjection x h).length =
      4 * x.cut.val + (if x.cut.val < 6 then 4 else 0) := by
  by_cases hc : x.cut.val < 6
  · simp [expandProjection, hc]
  · simp [expandProjection, hc]

theorem expandProjection_length_le_24 (x : Node) (h : 2 ≤ x.holes) :
    (expandProjection x h).length ≤ 24 := by
  rw [expandProjection_length]
  have hcut : x.cut.val ≤ 6 := by omega
  by_cases hc : x.cut.val < 6 <;> simp [hc] <;> omega

theorem expandProjection_mass_lt (x : Node) (h : 2 ≤ x.holes) :
    mass (expandProjection x h) < weight x := by
  let k : Nat := 25 ^ (x.holes - 1)
  have hk : 0 < k := by
    dsimp [k]
    exact Nat.pow_pos (by decide : 0 < 25) _
  have hcut : x.cut.val ≤ 6 := by omega
  have hcnt : 4 * x.cut.val + (if x.cut.val < 6 then 4 else 0) ≤ 24 := by
    by_cases hc : x.cut.val < 6 <;> simp [hc] <;> omega
  have hfactor :
      4 * x.cut.val * k + (if x.cut.val < 6 then 4 * k else 0) =
        (4 * x.cut.val + (if x.cut.val < 6 then 4 else 0)) * k := by
    by_cases hc : x.cut.val < 6 <;>
      simp [hc, Nat.add_mul, Nat.mul_assoc]
  have hn : x.holes - 1 + 1 = x.holes := by omega
  have hpow : 25 ^ x.holes = 25 * k := by
    rw [← hn, Nat.pow_succ]
    simp [k, Nat.mul_comm]
  have hbound :
      (4 * x.cut.val + (if x.cut.val < 6 then 4 else 0)) * k ≤ 24 * k :=
    Nat.mul_le_mul_right k hcnt
  have hstrict : 24 * k < 25 * k := by omega
  have hcalc :
      mass (expandProjection x h) =
        4 * x.cut.val * k + (if x.cut.val < 6 then 4 * k else 0) := by
    by_cases hc : x.cut.val < 6
    · simp [expandProjection, hc, mass_append, mass_replicate,
        existingChild, freshChild, weight, k]
    · simp [expandProjection, hc, mass_append, mass_replicate,
        existingChild, freshChild, weight, k]
  calc
    mass (expandProjection x h)
        = 4 * x.cut.val * k + (if x.cut.val < 6 then 4 * k else 0) := hcalc
    _ = (4 * x.cut.val + (if x.cut.val < 6 then 4 else 0)) * k := hfactor
    _ ≤ 24 * k := hbound
    _ < 25 * k := hstrict
    _ = 25 ^ x.holes := hpow.symm

theorem expandProjection'_mass_lt (x : Node) :
    mass (expandProjection' x) < weight x := by
  unfold expandProjection'
  by_cases h : x.holes = 1
  · simp [h, mass, weight]
  · have hp : 1 ≤ x.holes := x.holes_pos
    have htwo : 2 ≤ x.holes := by omega
    simpa [h] using expandProjection_mass_lt x htwo

inductive Verdict where
  | halt
  | nonhalt
  | unknown
deriving DecidableEq

structure SearchQueue where
  active : List Node
  holdout : List Node

def update (decide : Node → Verdict) (q : SearchQueue) : SearchQueue :=
  match q.active with
  | [] => q
  | x :: xs =>
    match decide x with
    | .halt => ⟨expandProjection' x ++ xs, q.holdout⟩
    | .nonhalt => ⟨xs, q.holdout⟩
    | .unknown => ⟨xs, x :: q.holdout⟩

theorem update_active_mass_lt (decide : Node → Verdict) (q : SearchQueue)
    (hne : q.active ≠ []) :
    mass (update decide q).active < mass q.active := by
  cases hq : q.active with
  | nil => exact False.elim (hne hq)
  | cons x xs =>
    cases hd : decide x with
    | halt =>
        simp [update, hq, hd, mass_append]
        exact Nat.add_lt_add_right (expandProjection'_mass_lt x) (mass xs)
    | nonhalt =>
        simp [update, hq, hd, mass]
        exact Nat.lt_add_of_pos_left (weight_pos x)
    | unknown =>
        simp [update, hq, hd, mass]
        exact Nat.lt_add_of_pos_left (weight_pos x)

/-- The source's non-BFS `SearchQueue_upds`, with its stop-on-empty behavior. -/
def runUpdates (decide : Node → Verdict) : Nat → SearchQueue → SearchQueue
  | 0, q => q
  | n + 1, q =>
    match q.active with
    | [] => q
    | _ :: _ => runUpdates decide n (update decide q)

theorem mass_zero_iff_nil (xs : List Node) :
    mass xs = 0 ↔ xs = [] := by
  cases xs with
  | nil => simp [mass]
  | cons x xs =>
      constructor
      · intro h
        have hw := weight_pos x
        simp [mass] at h
        omega
      · intro h
        cases h

theorem runUpdates_active_empty_of_bound (decide : Node → Verdict)
    (fuel : Nat) (q : SearchQueue) (hbound : mass q.active ≤ fuel) :
    (runUpdates decide fuel q).active = [] := by
  induction fuel generalizing q with
  | zero =>
      have hmass : mass q.active = 0 := by omega
      have hnil : q.active = [] := (mass_zero_iff_nil q.active).mp hmass
      simp [runUpdates, hnil]
  | succ fuel ih =>
      cases hq : q.active with
      | nil => simp [runUpdates, hq]
      | cons x xs =>
          have hdec := update_active_mass_lt decide q (by simp [hq])
          have hnext : mass (update decide q).active ≤ fuel := by omega
          simpa [runUpdates, hq] using ih (update decide q) hnext

/-- One source BFS pass: process exactly the initial active list, append
children/unknowns to the holdout list, then reset holdouts to active. -/
def bfsAux (decide : Node → Verdict) : List Node → List Node → List Node
  | [], holdout => holdout
  | x :: xs, holdout =>
    match decide x with
    | .halt => bfsAux decide xs (expandProjection' x ++ holdout)
    | .nonhalt => bfsAux decide xs holdout
    | .unknown => bfsAux decide xs (x :: holdout)

def bfsRound (decide : Node → Verdict) (q : SearchQueue) : SearchQueue :=
  ⟨bfsAux decide q.active q.holdout, []⟩

def totalMass (q : SearchQueue) : Nat := mass q.active + mass q.holdout

theorem bfsAux_mass_le (decide : Node → Verdict) :
    ∀ xs holdout, mass (bfsAux decide xs holdout) ≤ mass xs + mass holdout := by
  intro xs
  induction xs with
  | nil =>
      intro holdout
      simp [bfsAux, mass]
  | cons x xs ih =>
      intro holdout
      cases hd : decide x with
      | halt =>
          have hrec := ih (expandProjection' x ++ holdout)
          rw [mass_append] at hrec
          have hchild := expandProjection'_mass_lt x
          simp only [bfsAux, hd, mass]
          omega
      | nonhalt =>
          have hrec := ih holdout
          simp only [bfsAux, hd, mass]
          omega
      | unknown =>
          have hrec := ih (x :: holdout)
          simp [mass] at hrec
          simp only [bfsAux, hd, mass]
          omega

theorem bfsRound_total_mass_le (decide : Node → Verdict) (q : SearchQueue) :
    totalMass (bfsRound decide q) ≤ totalMass q := by
  unfold totalMass bfsRound
  simp [mass]
  exact bfsAux_mass_le decide q.active q.holdout

/-- Four source BFS passes, matching the definition of `q_0`. -/
def fourBfsPasses (decide : Node → Verdict) (q : SearchQueue) : SearchQueue :=
  bfsRound decide (bfsRound decide (bfsRound decide (bfsRound decide q)))

theorem fourBfsPasses_total_mass_le (decide : Node → Verdict) (q : SearchQueue) :
    totalMass (fourBfsPasses decide q) ≤ totalMass q := by
  unfold fourBfsPasses
  have h1 := bfsRound_total_mass_le decide
    (bfsRound decide (bfsRound decide (bfsRound decide q)))
  have h2 := bfsRound_total_mass_le decide
    (bfsRound decide (bfsRound decide q))
  have h3 := bfsRound_total_mass_le decide (bfsRound decide q)
  have h4 := bfsRound_total_mass_le decide q
  exact Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_trans h3 h4))

def rootNode : Node := ⟨11, by decide, ⟨2, by decide⟩⟩

def rootQueue : SearchQueue := ⟨[rootNode], []⟩

def q0 (decide : Node → Verdict) : SearchQueue :=
  fourBfsPasses decide rootQueue

theorem q0_total_mass_le (decide : Node → Verdict) :
    totalMass (q0 decide) ≤ 25 ^ 11 := by
  have hroot : totalMass rootQueue = 25 ^ 11 := by
    simp [totalMass, rootQueue, rootNode, mass, weight]
  exact Nat.le_trans (fourBfsPasses_total_mass_le decide rootQueue) (le_of_eq hroot)

def chunkQueue (q : SearchQueue) (l sz : Nat) : SearchQueue :=
  ⟨(q.active.drop l).take sz, q.holdout⟩

theorem mass_take_le (xs : List Node) (n : Nat) :
    mass (xs.take n) ≤ mass xs := by
  induction xs generalizing n with
  | nil => simp [mass]
  | cons x xs ih =>
      cases n with
      | zero => simp [mass]
      | succ n =>
          have h := ih n
          simp [mass] at h ⊢
          omega

theorem mass_drop_le (xs : List Node) (n : Nat) :
    mass (xs.drop n) ≤ mass xs := by
  induction xs generalizing n with
  | nil => simp [mass]
  | cons x xs ih =>
      cases n with
      | zero => simp [mass]
      | succ n =>
          have h := ih n
          simp [mass] at h ⊢
          omega

theorem mass_chunk_le (xs : List Node) (l sz : Nat) :
    mass ((xs.drop l).take sz) ≤ mass xs := by
  calc
    mass ((xs.drop l).take sz) ≤ mass (xs.drop l) := mass_take_le (xs.drop l) sz
    _ ≤ mass xs := mass_drop_le xs l

theorem chunk_active_mass_le (q : SearchQueue) (l sz : Nat) :
    mass (chunkQueue q l sz).active ≤ totalMass q := by
  change mass ((q.active.drop l).take sz) ≤ mass q.active + mass q.holdout
  have h := mass_chunk_le q.active l sz
  omega

theorem q0_holdout_empty (decide : Node → Verdict) :
    (q0 decide).holdout = [] := by
  simp [q0, fourBfsPasses, bfsRound]

def maxT : Nat := 2 ^ 60

theorem maxT_ge_25_pow_11 : 25 ^ 11 ≤ maxT := by
  decide

/-- Every `q_i l sz` slice of the four-pass queue drains before the pinned
`MAXT=2^60` fuel is exhausted, for every decider. -/
theorem every_chunk_drains (decide : Node → Verdict) (l sz : Nat) :
    (runUpdates decide maxT (chunkQueue (q0 decide) l sz)).active = [] := by
  apply runUpdates_active_empty_of_bound
  have hchunk := chunk_active_mass_le (q0 decide) l sz
  have hq0 := q0_total_mass_le decide
  have hmax := maxT_ge_25_pow_11
  exact Nat.le_trans (Nat.le_trans hchunk hq0) hmax

#print axioms expandProjection_length
#print axioms expandProjection_length_le_24
#print axioms expandProjection_mass_lt
#print axioms expandProjection'_mass_lt
#print axioms update_active_mass_lt
#print axioms runUpdates_active_empty_of_bound
#print axioms bfsRound_total_mass_le
#print axioms fourBfsPasses_total_mass_le
#print axioms q0_total_mass_le
#print axioms chunk_active_mass_le
#print axioms every_chunk_drains

end BB6.Agent48Queue
