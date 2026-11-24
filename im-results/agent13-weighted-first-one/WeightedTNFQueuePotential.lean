import Std
import WeightedTNFCertificate

namespace BB6.Agent13BlankDelay

/-- The potential-relevant projection of an upstream TNF node. The actual
    machine table is intentionally erased; `holes` and `fresh` are exactly
    `num_undef_trans` and `min_unused_state` from Enumerate62.v. -/
structure QueueNode where
  holes : Nat
  fresh : Nat
  deriving DecidableEq, Repr

def queueNodeWeight (x : QueueNode) : Nat := 25 ^ x.holes

def queueListWeight : List QueueNode → Nat
  | [] => 0
  | x :: xs => queueNodeWeight x + queueListWeight xs

theorem queueListWeight_append (xs ys : List QueueNode) :
    queueListWeight (xs ++ ys) = queueListWeight xs + queueListWeight ys := by
  induction xs with
  | nil => simp [queueListWeight]
  | cons x xs ih =>
      simp [queueListWeight, ih, Nat.add_assoc]

theorem queueListWeight_map_uniform (fs : List Nat) (n : Nat) :
    queueListWeight (fs.map (fun f => ({ holes := n, fresh := f } : QueueNode))) =
      fs.length * 25 ^ n := by
  induction fs with
  | nil => simp [queueListWeight]
  | cons f fs ih =>
      simp [queueListWeight, queueNodeWeight, ih, Nat.succ_mul]
  omega

/-- Exact fresh-label multiplicities in the pinned upstream `expand`:
    four write/direction choices for each existing state, plus four for
    the least fresh state unless all six states have been introduced. -/
def sourceFreshes (m : Nat) : List Nat :=
  List.replicate (4 * m) m ++
    (if m < 6 then List.replicate 4 (m + 1) else [])

theorem sourceFreshes_length_le24 (m : Nat) (hm : m ≤ 6) :
    (sourceFreshes m).length ≤ 24 := by
  by_cases h : m < 6
  · simp [sourceFreshes, h]
    omega
  · simp [sourceFreshes, h]
    omega

/-- Exact projection of upstream `expand'` to its two integer node fields.
    At one remaining undefined row, upstream `expand'` returns no children. -/
def sourceExpand (n m : Nat) : List QueueNode :=
  if n = 1 then []
  else (sourceFreshes m).map (fun f => ({ holes := n - 1, fresh := f } : QueueNode))

theorem sourceExpand_length_le24 (n m : Nat) (hn : 1 < n) (hm : m ≤ 6) :
    (sourceExpand n m).length ≤ 24 := by
  simp [sourceExpand, Nat.ne_of_gt hn, sourceFreshes_length_le24 m hm]

theorem sourceExpand_weight_eq (n m : Nat) (hn : 1 < n) :
    queueListWeight (sourceExpand n m) =
      (sourceFreshes m).length * 25 ^ (n - 1) := by
  simp [sourceExpand, Nat.ne_of_gt hn, queueListWeight_map_uniform]

/-- The source expansion preserves the valid-node invariant. -/
theorem sourceExpand_valid (n m : Nat) (hn : 1 ≤ n) (hm : m ≤ 6) :
    ∀ x, x ∈ sourceExpand n m → 1 ≤ x.holes ∧ x.fresh ≤ 6 := by
  intro x hx
  have hne : n ≠ 1 := by
    intro h
    subst n
    simp [sourceExpand] at hx
  have hgt : 1 < n := by omega
  simp [sourceExpand, hne] at hx
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hx
  constructor
  · omega
  · simp only [sourceFreshes, List.mem_append] at hf
    rcases hf with hf | hf
    · rcases List.mem_replicate.mp hf with ⟨_, hEq⟩
      omega
    · by_cases hlt : m < 6
      · simp [hlt] at hf
        rcases List.mem_replicate.mp hf with ⟨_, hEq⟩
        omega
      · simp [hlt] at hf

theorem queueListWeight_le_length_mul (xs : List QueueNode) (k : Nat)
    (h : ∀ x, x ∈ xs → queueNodeWeight x ≤ k) :
    queueListWeight xs ≤ xs.length * k := by
  induction xs with
  | nil => simp [queueListWeight]
  | cons x xs ih =>
      have hx := h x (by simp)
      have hxs : ∀ y, y ∈ xs → queueNodeWeight y ≤ k := by
        intro y hy
        exact h y (by simp [hy])
      have ih' := ih hxs
      simp [queueListWeight, Nat.succ_mul] at *
      omega

/-- Each nonempty source expansion has at most 24 children, all with one
    fewer undefined rows. Since 24 < 25, its 25-adic potential strictly
    decreases. This is the core MAXT bound. -/
theorem sourceExpand_weight_lt (n m : Nat) (hn : 1 ≤ n) (hm : m ≤ 6) :
    queueListWeight (sourceExpand n m) < 25 ^ n := by
  by_cases h1 : n = 1
  · simp [sourceExpand, h1, queueListWeight]
  · have hn' : 1 < n := by omega
    rw [sourceExpand_weight_eq n m hn']
    have hlen := sourceFreshes_length_le24 m hm
    have hpow : 0 < 25 ^ (n - 1) :=
      Nat.pow_pos (by decide : 0 < 25)
    have hmul :
        (sourceFreshes m).length * 25 ^ (n - 1) ≤
          24 * 25 ^ (n - 1) :=
      Nat.mul_le_mul_right (25 ^ (n - 1)) hlen
    have hstep : 24 * 25 ^ (n - 1) < 25 ^ n := by
      calc
        24 * 25 ^ (n - 1) < 25 * 25 ^ (n - 1) :=
          Nat.mul_lt_mul_of_pos_right (by omega) hpow
        _ = 25 ^ (n - 1) * 25 := by omega
        _ = 25 ^ ((n - 1) + 1) := by rw [← Nat.pow_succ]
        _ = 25 ^ n := by congr 1; omega
    exact Nat.lt_of_le_of_lt hmul hstep

inductive QueueVerdict where
  | halt
  | nonhalt
  | unknown
  deriving DecidableEq, Repr

structure SearchQueue where
  active : List QueueNode
  holdout : List QueueNode

def QueueNodeValid (x : QueueNode) : Prop :=
  1 ≤ x.holes ∧ x.fresh ≤ 6

def QueueListValid (xs : List QueueNode) : Prop :=
  ∀ x, x ∈ xs → QueueNodeValid x

def SearchQueueValid (q : SearchQueue) : Prop :=
  QueueListValid q.active ∧ QueueListValid q.holdout

def totalPotential (q : SearchQueue) : Nat :=
  queueListWeight q.active + queueListWeight q.holdout

def activePotential (q : SearchQueue) : Nat :=
  queueListWeight q.active

/-- One exact BFS pass over the active list. Halt children and unknown nodes
    are held for the next pass; the terminal reset moves the holdout list back
    to the active queue. This is the two-list recurrence in Enumerate62.v. -/
def bfsPass (f : QueueNode → QueueVerdict) :
    List QueueNode → List QueueNode → SearchQueue
  | [], hold => ⟨hold, []⟩
  | x :: xs, hold =>
      match f x with
      | .halt => bfsPass f xs (sourceExpand x.holes x.fresh ++ hold)
      | .nonhalt => bfsPass f xs hold
      | .unknown => bfsPass f xs (x :: hold)

def bfsRound (f : QueueNode → QueueVerdict) (q : SearchQueue) : SearchQueue :=
  bfsPass f q.active q.holdout

theorem bfsPass_valid (f : QueueNode → QueueVerdict) :
    ∀ xs hold, QueueListValid xs → QueueListValid hold →
      SearchQueueValid (bfsPass f xs hold) := by
  intro xs
  induction xs with
  | nil =>
      intro hold hxs hhold
      exact ⟨hhold, by intro x hx; cases hx⟩
  | cons x xs ih =>
      intro hold hxs hhold
      have hx : QueueNodeValid x := hxs x (by simp)
      have hxs' : QueueListValid xs := by
        intro y hy
        exact hxs y (by simp [hy])
      cases hdec : f x with
      | halt =>
          simp only [bfsPass, hdec]
          have hchildren := sourceExpand_valid x.holes x.fresh hx.1 hx.2
          have hhold' : QueueListValid (sourceExpand x.holes x.fresh ++ hold) := by
            intro y hy
            rcases List.mem_append.mp hy with hy | hy
            · exact hchildren y hy
            · exact hhold y hy
          exact ih (sourceExpand x.holes x.fresh ++ hold) hxs' hhold'
      | nonhalt =>
          simp only [bfsPass, hdec]
          exact ih hold hxs' hhold
      | unknown =>
          simp only [bfsPass, hdec]
          have hhold' : QueueListValid (x :: hold) := by
            intro y hy
            simp only [List.mem_cons] at hy
            rcases hy with hEq | hy
            · cases hEq
              exact hx
            · exact hhold y hy
          exact ih (x :: hold) hxs' hhold'

theorem bfsPass_potential_le (f : QueueNode → QueueVerdict) :
    ∀ xs hold, QueueListValid xs → QueueListValid hold →
      totalPotential (bfsPass f xs hold) ≤
        queueListWeight xs + queueListWeight hold := by
  intro xs
  induction xs with
  | nil =>
      intro hold hxs hhold
      simp [bfsPass, totalPotential, Nat.add_comm]
  | cons x xs ih =>
      intro hold hxs hhold
      have hx : QueueNodeValid x := hxs x (by simp)
      have hxs' : QueueListValid xs := by
        intro y hy
        exact hxs y (by simp [hy])
      cases hdec : f x with
      | halt =>
          have hchildren := sourceExpand_valid x.holes x.fresh hx.1 hx.2
          have hhold' : QueueListValid (sourceExpand x.holes x.fresh ++ hold) := by
            intro y hy
            rcases List.mem_append.mp hy with hy | hy
            · exact hchildren y hy
            · exact hhold y hy
          have hIH := ih (sourceExpand x.holes x.fresh ++ hold) hxs' hhold'
          have hweight := sourceExpand_weight_lt x.holes x.fresh hx.1 hx.2
          have hlocal :
              queueListWeight (sourceExpand x.holes x.fresh ++ hold) ≤
                queueNodeWeight x + queueListWeight hold := by
            rw [queueListWeight_append]
            simp [queueNodeWeight] at hweight ⊢
            omega
          simp only [bfsPass, hdec]
          have h := Nat.le_trans hIH
            (Nat.add_le_add_left hlocal (queueListWeight xs))
          simpa [totalPotential, queueListWeight, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using h
      | nonhalt =>
          have hIH := ih hold hxs' hhold
          simp only [bfsPass, hdec]
          simpa [totalPotential, queueListWeight] using
            (Nat.le_trans hIH (by omega : queueListWeight xs + queueListWeight hold ≤
              queueNodeWeight x + queueListWeight xs + queueListWeight hold))
      | unknown =>
          have hhold' : QueueListValid (x :: hold) := by
            intro y hy
            simp only [List.mem_cons] at hy
            rcases hy with hEq | hy
            · cases hEq
              exact hx
            · exact hhold y hy
          have hIH := ih (x :: hold) hxs' hhold'
          simp only [bfsPass, hdec]
          simpa [totalPotential, queueListWeight, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using hIH

theorem bfsRound_valid (f : QueueNode → QueueVerdict) (q : SearchQueue)
    (hq : SearchQueueValid q) :
    SearchQueueValid (bfsRound f q) :=
  bfsPass_valid f q.active q.holdout hq.1 hq.2

theorem bfsRound_potential_le (f : QueueNode → QueueVerdict) (q : SearchQueue)
    (hq : SearchQueueValid q) :
    totalPotential (bfsRound f q) ≤ totalPotential q := by
  simpa [bfsRound, totalPotential] using
    (bfsPass_potential_le f q.active q.holdout hq.1 hq.2)

def bfsRounds (f : QueueNode → QueueVerdict) : Nat → SearchQueue → SearchQueue
  | 0, q => q
  | n + 1, q => bfsRounds f n (bfsRound f q)

theorem bfsRounds_valid (f : QueueNode → QueueVerdict) :
    ∀ n q, SearchQueueValid q → SearchQueueValid (bfsRounds f n q) := by
  intro n
  induction n with
  | zero =>
      intro q hq
      simpa [bfsRounds] using hq
  | succ n ih =>
      intro q hq
      exact ih (bfsRound f q) (bfsRound_valid f q hq)

theorem bfsRounds_potential_le (f : QueueNode → QueueVerdict) :
    ∀ n q, SearchQueueValid q →
      totalPotential (bfsRounds f n q) ≤ totalPotential q := by
  intro n
  induction n with
  | zero =>
      intro q hq
      simp [bfsRounds]
  | succ n ih =>
      intro q hq
      have hq' := bfsRound_valid f q hq
      have h1 := ih (bfsRound f q) hq'
      have h2 := bfsRound_potential_le f q hq
      exact Nat.le_trans h1 h2

def rootQueueNode : QueueNode := ⟨11, 2⟩
def rootSearchQueue : SearchQueue := ⟨[rootQueueNode], []⟩

theorem rootSearchQueue_valid : SearchQueueValid rootSearchQueue := by
  constructor
  · intro x hx
    simp [rootSearchQueue, rootQueueNode] at hx
    subst x
    exact ⟨by decide, by decide⟩
  · intro x hx
    cases hx

theorem rootSearchQueue_potential :
    totalPotential rootSearchQueue = 25 ^ 11 := by
  simp [rootSearchQueue, rootQueueNode, totalPotential,
    queueListWeight, queueNodeWeight]

/-- Four upstream BFS passes, i.e. the projected `q_0`. -/
def projectedQ0 (f : QueueNode → QueueVerdict) : SearchQueue :=
  bfsRounds f 4 rootSearchQueue

theorem projectedQ0_valid (f : QueueNode → QueueVerdict) :
    SearchQueueValid (projectedQ0 f) :=
  bfsRounds_valid f 4 rootSearchQueue rootSearchQueue_valid

theorem projectedQ0_potential_le (f : QueueNode → QueueVerdict) :
    totalPotential (projectedQ0 f) ≤ 25 ^ 11 := by
  have h := bfsRounds_potential_le f 4 rootSearchQueue rootSearchQueue_valid
  rw [rootSearchQueue_potential] at h
  exact h

theorem queueListWeight_take_le (xs : List QueueNode) (n : Nat) :
    queueListWeight (xs.take n) ≤ queueListWeight xs := by
  induction xs generalizing n with
  | nil => simp [queueListWeight]
  | cons x xs ih =>
      cases n with
      | zero => simp [queueListWeight]
      | succ n =>
          have h := ih n
          simp [List.take, queueListWeight] at *
          omega

theorem queueListWeight_drop_le (xs : List QueueNode) (n : Nat) :
    queueListWeight (xs.drop n) ≤ queueListWeight xs := by
  induction n generalizing xs with
  | zero => simp [List.drop]
  | succ n ih =>
      cases xs with
      | nil => simp [List.drop, queueListWeight]
      | cons x xs =>
          have h := ih xs
          simp [List.drop, queueListWeight] at *
          omega

theorem queueListValid_take (xs : List QueueNode) (hxs : QueueListValid xs)
    (n : Nat) : QueueListValid (xs.take n) := by
  induction xs generalizing n with
  | nil => simp [QueueListValid]
  | cons x xs ih =>
      cases n with
      | zero => simp [QueueListValid]
      | succ n =>
          have hx : QueueNodeValid x := hxs x (by simp)
          have htail : QueueListValid xs := by
            intro y hy
            exact hxs y (by simp [hy])
          have ht := ih htail n
          intro y hy
          simp [List.take, List.mem_cons] at hy
          rcases hy with hEq | hy
          · cases hEq
            exact hx
          · exact ht y hy

theorem queueListValid_drop (xs : List QueueNode) (hxs : QueueListValid xs)
    (n : Nat) : QueueListValid (xs.drop n) := by
  induction n generalizing xs hxs with
  | zero => simpa [List.drop] using hxs
  | succ n ih =>
      cases xs with
      | nil => simp [QueueListValid]
      | cons x xs =>
          apply ih
          intro y hy
          exact hxs y (by simp [hy])

/-- The exact projected `q_i(l,sz)`: take `sz` entries after dropping `l`
    from the active part of `q_0`, retaining the common holdout list. -/
def projectedQI (f : QueueNode → QueueVerdict) (l sz : Nat) : SearchQueue :=
  ⟨((projectedQ0 f).active.drop l).take sz, (projectedQ0 f).holdout⟩

theorem projectedQI_valid (f : QueueNode → QueueVerdict) (l sz : Nat) :
    SearchQueueValid (projectedQI f l sz) := by
  have hq := projectedQ0_valid f
  exact ⟨
    queueListValid_take ((projectedQ0 f).active.drop l)
      (queueListValid_drop (projectedQ0 f).active hq.1 l) sz,
    hq.2
  ⟩

theorem projectedQI_potential_le (f : QueueNode → QueueVerdict) (l sz : Nat) :
    totalPotential (projectedQI f l sz) ≤ totalPotential (projectedQ0 f) := by
  have hdrop := queueListWeight_drop_le (projectedQ0 f).active l
  have htake := queueListWeight_take_le ((projectedQ0 f).active.drop l) sz
  simp [projectedQI, totalPotential]
  omega

def serialUpdate (f : QueueNode → QueueVerdict) (q : SearchQueue) : SearchQueue :=
  match q.active with
  | [] => q
  | x :: xs =>
      match f x with
      | .halt => ⟨sourceExpand x.holes x.fresh ++ xs, q.holdout⟩
      | .nonhalt => ⟨xs, q.holdout⟩
      | .unknown => ⟨xs, x :: q.holdout⟩

theorem serialUpdate_valid (f : QueueNode → QueueVerdict) (q : SearchQueue)
    (hq : SearchQueueValid q) :
    SearchQueueValid (serialUpdate f q) := by
  cases q with
  | mk active hold =>
      cases active with
      | nil => simpa [serialUpdate] using hq
      | cons x xs =>
          have hx : QueueNodeValid x := hq.1 x (by simp)
          have hxs : QueueListValid xs := by
            intro y hy
            exact hq.1 y (by simp [hy])
          cases hdec : f x with
          | halt =>
              simp only [serialUpdate, hdec]
              have hc := sourceExpand_valid x.holes x.fresh hx.1 hx.2
              have ha : QueueListValid (sourceExpand x.holes x.fresh ++ xs) := by
                intro y hy
                rcases List.mem_append.mp hy with hy | hy
                · exact hc y hy
                · exact hxs y hy
              exact ⟨ha, hq.2⟩
          | nonhalt =>
              simp only [serialUpdate, hdec]
              exact ⟨hxs, hq.2⟩
          | unknown =>
              simp only [serialUpdate, hdec]
              have hh : QueueListValid (x :: hold) := by
                intro y hy
                simp only [List.mem_cons] at hy
                rcases hy with hEq | hy
                · cases hEq
                  exact hx
                · exact hq.2 y hy
              exact ⟨hxs, hh⟩

theorem activePotential_serialUpdate_lt (f : QueueNode → QueueVerdict)
    (q : SearchQueue) (hq : SearchQueueValid q) (hne : q.active ≠ []) :
    activePotential (serialUpdate f q) < activePotential q := by
  cases q with
  | mk active hold =>
      cases active with
      | nil => contradiction
      | cons x xs =>
          have hx : QueueNodeValid x := hq.1 x (by simp)
          cases hdec : f x with
          | halt =>
              have hlt := sourceExpand_weight_lt x.holes x.fresh hx.1 hx.2
              simp [serialUpdate, hdec, activePotential, queueListWeight_append]
              exact Nat.add_lt_add_right hlt (queueListWeight xs)
          | nonhalt =>
              have hpos : 0 < queueNodeWeight x :=
                Nat.pow_pos (by decide : 0 < 25)
              simp [serialUpdate, hdec, activePotential, queueListWeight]
              omega
          | unknown =>
              have hpos : 0 < queueNodeWeight x :=
                Nat.pow_pos (by decide : 0 < 25)
              simp [serialUpdate, hdec, activePotential, queueListWeight]
              omega

def serialRun (f : QueueNode → QueueVerdict) : Nat → SearchQueue → SearchQueue
  | 0, q => q
  | n + 1, q => serialRun f n (serialUpdate f q)

theorem serialRun_empty_of_potential (f : QueueNode → QueueVerdict) :
    ∀ fuel q, SearchQueueValid q → activePotential q ≤ fuel →
      (serialRun f fuel q).active = [] := by
  intro fuel
  induction fuel with
  | zero =>
      intro q hq hpot
      cases q with
      | mk active hold =>
          cases active with
          | nil => rfl
          | cons x xs =>
              have hx : QueueNodeValid x := hq.1 x (by simp)
              have hpos : 0 < queueNodeWeight x :=
                Nat.pow_pos (by decide : 0 < 25)
              simp [activePotential, queueListWeight] at hpot
              omega
  | succ fuel ih =>
      intro q hq hpot
      by_cases he : q.active = []
      · have hzero : activePotential q = 0 := by
          simp [activePotential, queueListWeight, he]
        have hpot' : activePotential q ≤ fuel := by omega
        have h := ih q hq hpot'
        simpa [serialRun, serialUpdate, he] using h
      · have hlt := activePotential_serialUpdate_lt f q hq he
        have hq' := serialUpdate_valid f q hq
        have hpot' : activePotential (serialUpdate f q) ≤ fuel := by omega
        exact ih (serialUpdate f q) hq' hpot'

/-- The fixed source constant is far larger than the initial potential. -/
theorem sourceMAXT_bound : 25 ^ 11 < 2 ^ 60 := by
  decide

theorem activePotential_le_total (q : SearchQueue) :
    activePotential q ≤ totalPotential q := by
  simp [activePotential, totalPotential]

/-- Every source `q_i(l,sz)` chunk drains its active queue before MAXT.
    This theorem is independent of the chunk size and of all decider outcomes. -/
theorem projectedQI_drains (f : QueueNode → QueueVerdict) (l sz : Nat) :
    (serialRun f (2 ^ 60) (projectedQI f l sz)).active = [] := by
  apply serialRun_empty_of_potential
  · exact projectedQI_valid f l sz
  · have h1 := activePotential_le_total (projectedQI f l sz)
    have h2 := projectedQI_potential_le f l sz
    have h3 := projectedQ0_potential_le f
    have h4 := sourceMAXT_bound
    omega

#print axioms sourceFreshes_length_le24
#print axioms sourceExpand_valid
#print axioms sourceExpand_weight_lt
#print axioms bfsPass_valid
#print axioms bfsPass_potential_le
#print axioms projectedQ0_potential_le
#print axioms projectedQI_potential_le
#print axioms activePotential_serialUpdate_lt
#print axioms serialRun_empty_of_potential
#print axioms projectedQI_drains

end BB6.Agent13BlankDelay
