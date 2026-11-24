import Boundary
import DTableWitness
import Lean.Elab.Tactic.Omega

namespace BB6.BoundaryPortfolio
open BB6.Portfolio
abbrev B := CryptidBoundary.Cfg

/-- Signed head-relative tape, with an implicit infinite zero tail. -/
def cell (c : B) : Int → Bool
  | .ofNat 0 => c.h
  | .ofNat (n+1) => c.r[n]?.getD false
  | .negSucc n => c.l[n]?.getD false

def absoluteTape (c : B) (h : Int) : Int → Bool := fun i => cell c (i-h)

private theorem ofNat_succ_add_one (n : Nat) :
    (Int.ofNat (n+1)) + 1 = Int.ofNat (n+2) := by simp only [Int.ofNat_eq_coe]; omega
private theorem negSucc_succ_add_one (n : Nat) :
    (Int.negSucc (n+1)) + 1 = Int.negSucc n := by omega
private theorem ofNat_succ_sub_one (n : Nat) :
    (Int.ofNat (n+1)) - 1 = Int.ofNat n := by simp only [Int.ofNat_eq_coe]; omega
private theorem negSucc_sub_one (n : Nat) :
    (Int.negSucc n) - 1 = Int.negSucc (n+1) := by omega

theorem cell_goR (c : B) (w : Bool) (s : Nat) (i : Int) :
    cell (CryptidBoundary.goR c w s) i = if i = -1 then w else cell c (i+1) := by
  rcases c with ⟨l,b,r,st⟩
  cases i with
  | ofNat n =>
    cases n with
    | zero => cases r <;> rfl
    | succ n =>
      rw [ofNat_succ_add_one]
      have hn : Int.ofNat (n+1) ≠ -1 := by simp only [Int.ofNat_eq_coe]; omega
      simp only [if_neg hn]
      cases r <;> rfl
  | negSucc n =>
    cases n with
    | zero => cases r <;> rfl
    | succ n =>
      rw [negSucc_succ_add_one]
      have hn : Int.negSucc (n+1) ≠ -1 := by omega
      simp only [if_neg hn]
      cases r <;> rfl

theorem cell_goL (c : B) (w : Bool) (s : Nat) (i : Int) :
    cell (CryptidBoundary.goL c w s) i = if i = 1 then w else cell c (i-1) := by
  rcases c with ⟨l,b,r,st⟩
  cases i with
  | ofNat n =>
    cases n with
    | zero => cases l <;> rfl
    | succ n =>
      cases n with
      | zero => cases l <;> rfl
      | succ n =>
        rw [ofNat_succ_sub_one]
        have hn : Int.ofNat (n+1+1) ≠ 1 := by simp only [Int.ofNat_eq_coe]; omega
        simp only [if_neg hn]
        cases l <;> rfl
  | negSucc n =>
    rw [negSucc_sub_one]
    have hn : Int.negSucc n ≠ 1 := by omega
    simp only [if_neg hn]
    cases l <;> rfl

theorem tape_goR (c : B) (w : Bool) (s : Nat) (h : Int) :
    absoluteTape (CryptidBoundary.goR c w s) (h+1) = updateTape (absoluteTape c h) h w := by
  funext i
  unfold absoluteTape updateTape
  rw [cell_goR]
  by_cases e : i = h
  · subst i; rw [if_pos (show h-(h+1) = -1 by omega), if_pos rfl]
  · have he : i-(h+1) ≠ -1 := by omega
    rw [if_neg he, if_neg e]
    congr 1 <;> omega

theorem tape_goL (c : B) (w : Bool) (s : Nat) (h : Int) :
    absoluteTape (CryptidBoundary.goL c w s) (h-1) = updateTape (absoluteTape c h) h w := by
  funext i
  unfold absoluteTape updateTape
  rw [cell_goL]
  by_cases e : i = h
  · subst i; rw [if_pos (show h-(h-1) = 1 by omega), if_pos rfl]
  · have he : i-(h-1) ≠ 1 := by omega
    rw [if_neg he, if_neg e]
    congr 1 <;> omega


/-- The total interpreter's states outside the six live states project to none. -/
def project (c : B) (h : Int) : Option Cfg :=
  if c.st < 6 then some ⟨Fin.ofNat 6 c.st, h, absoluteTape c h⟩ else none

def motion (c : B) : Int :=
  if c.st = 0 ∨ (c.st = 1 ∧ c.h = true) then 1
  else if c.st < 6 ∧ (c.st ≠ 5 ∨ c.h = false) then -1 else 0

@[simp] theorem project_none_iff (c : B) (h : Int) : project c h = none ↔ 6 ≤ c.st := by
  unfold project
  split <;> simp_all <;> omega

@[simp] theorem cell_head (c : B) (h : Int) : absoluteTape c h h = c.h := by
  simp [absoluteTape, cell]

@[simp] theorem goR_st (c : B) (w : Bool) (s : Nat) : (CryptidBoundary.goR c w s).st = s := by
  cases c; simp [CryptidBoundary.goR]; split <;> rfl
@[simp] theorem goL_st (c : B) (w : Bool) (s : Nat) : (CryptidBoundary.goL c w s).st = s := by
  cases c; simp [CryptidBoundary.goL]; split <;> rfl

/-- Exact one-step square, including the transition from F/1 to the sink. -/
theorem project_step (c : B) (h : Int) :
    project (CryptidBoundary.step c) (h+motion c) = (project c h).bind (step D0) := by
  rcases c with ⟨l,b,r,s⟩
  rcases s with (_|_|_|_|_|_|s) <;> cases b <;>
    simp [CryptidBoundary.step, motion, project, step, D0, Dir.dx, tape_goR, tape_goL,
      show ∀ x : Int, x + -1 = x - 1 by intro x; omega] <;> try rfl <;>
    (have hh : ¬ (s + 1 + 1 + 1 + 1 + 1 + 1 < 6) := by omega; simp [hh])


/-- Track the physical head, even though the Boundary interpreter stores a
    head-relative tape. This adds no extra behavior to the source interpreter. -/
def positionedRun : Nat → B → Int → B × Int
  | 0, c, h => (c,h)
  | n+1, c, h =>
    let p := positionedRun n c h
    (CryptidBoundary.step p.1, p.2 + motion p.1)

theorem positionedRun_source (n : Nat) (c : B) (h : Int) :
    (positionedRun n c h).1 = CryptidBoundary.run n c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [positionedRun, ih]
    rw [CryptidBoundary.run_add]
    rfl

theorem project_run (n : Nat) (c : B) (h : Int) :
    project (positionedRun n c h).1 (positionedRun n c h).2 = run D0 n (project c h) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [positionedRun, run, project_step, ih]

theorem step_state_le (c : B) (hc : c.st ≤ 6) : (CryptidBoundary.step c).st ≤ 6 := by
  rcases c with ⟨l,b,r,s⟩
  rcases s with (_|_|_|_|_|_|s) <;> cases b <;> simp_all [CryptidBoundary.step] <;> omega

theorem run_state_le (n : Nat) (c : B) (hc : c.st ≤ 6) : (CryptidBoundary.run n c).st ≤ 6 := by
  induction n with
  | zero => exact hc
  | succ n ih =>
    rw [CryptidBoundary.run_add]
    exact step_state_le _ ih

def sourceBlank (s : State) : B := ⟨[],false,[],s.val⟩

@[simp] theorem project_blank (s : State) : project (sourceBlank s) 0 = some (blank s) := by
  have hs : s.val < 6 := s.isLt
  unfold project sourceBlank blank
  simp only [hs, if_true]
  congr 1
  congr 1
  · apply Fin.ext
    simp [Fin.ofNat, Nat.mod_eq_of_lt hs]
  · funext i
    simp [absoluteTape, Int.sub_zero]
    cases i with
    | ofNat n => cases n <;> rfl
    | negSucc n => rfl

/-- A raw halting event has a live final configuration and an undefined next
    transition. Boundary reaches state 6 on that next query, not before it. -/
def firstFrozen (c : B) (n : Nat) : Prop :=
  (CryptidBoundary.run n c).st < 6 ∧ (CryptidBoundary.run (n+1) c).st = 6

theorem raw_haltsAt_iff (s : State) (n : Nat) :
    haltsAt D0 s n ↔ firstFrozen (sourceBlank s) n := by
  let c := sourceBlank s
  have hr := project_run n c 0
  have hr1 := project_run (n+1) c 0
  rw [project_blank] at hr hr1
  have h1 : (CryptidBoundary.run (n+1) c).st ≤ 6 := run_state_le _ _ (by dsimp [c,sourceBlank]; omega)
  have hn : run D0 n (some (blank s)) ≠ none ↔ (CryptidBoundary.run n c).st < 6 := by
    rw [← hr, ne_eq, project_none_iff, positionedRun_source]
    omega
  have hn1 : run D0 (n+1) (some (blank s)) = none ↔ (CryptidBoundary.run (n+1) c).st = 6 := by
    rw [← hr1, project_none_iff, positionedRun_source]
    omega
  change haltsAt D0 s n ↔ (CryptidBoundary.run n c).st < 6 ∧ (CryptidBoundary.run (n+1) c).st = 6
  rw [← hn, ← hn1]
  unfold haltsAt
  cases h : run D0 n (some (blank s)) with
  | none => simp [run,h]
  | some d => simp [run,h]

theorem D1_haltsAt_iff (n : Nat) : haltsAt D1 0 n ↔ firstFrozen (sourceBlank 5) n :=
  (D1_exact_halt_time n).trans (raw_haltsAt_iff 5 n)
theorem D2_haltsAt_iff (n : Nat) : haltsAt D2 0 n ↔ firstFrozen (sourceBlank 2) n :=
  (D2_exact_halt_time n).trans (raw_haltsAt_iff 2 n)
theorem D3_haltsAt_iff (n : Nat) : haltsAt D3 0 n ↔ firstFrozen (sourceBlank 1) n :=
  (D3_exact_halt_time n).trans (raw_haltsAt_iff 1 n)


/-- The only live source gate is F/1. A sink observation one step later
    is equivalent to this exact gate at n live transitions. -/
theorem firstFrozen_gate (c : B) (n : Nat) :
    firstFrozen c n ↔ (CryptidBoundary.run n c).st = 5 ∧ (CryptidBoundary.run n c).h = true := by
  unfold firstFrozen
  rw [CryptidBoundary.run_add]
  change ((CryptidBoundary.run n c).st < 6 ∧ (CryptidBoundary.step (CryptidBoundary.run n c)).st = 6) ↔ _
  generalize CryptidBoundary.run n c = d
  rcases d with ⟨l,b,r,s⟩
  rcases s with (_|_|_|_|_|_|s) <;> cases b <;> simp [CryptidBoundary.step] <;> omega

theorem firstFrozen_prefix (c d : B) (p n : Nat) (hp : CryptidBoundary.run p c = d) :
    firstFrozen c (p+n) ↔ firstFrozen d n := by
  rw [firstFrozen_gate, firstFrozen_gate, CryptidBoundary.run_add, hp]

theorem exists_firstFrozen_iff (c : B) (hc : c.st < 6) :
    (∃ n, firstFrozen c n) ↔ ∃ n, (CryptidBoundary.run n c).st = 6 := by
  constructor
  · rintro ⟨n,_,hn⟩
    exact ⟨n+1,hn⟩
  · rintro ⟨n,hn⟩
    induction n with
    | zero => exact False.elim (by change c.st = 6 at hn; omega)
    | succ n ih =>
      by_cases hprev : (CryptidBoundary.run n c).st = 6
      · exact ih hprev
      · have hle := run_state_le n c (Nat.le_of_lt hc)
        exact ⟨n,by omega,hn⟩

theorem raw_halts_iff (s : State) :
    haltsFrom D0 s ↔ ∃ n, (CryptidBoundary.run n (sourceBlank s)).st = 6 := by
  change (∃ n, haltsAt D0 s n) ↔ _
  simp only [raw_haltsAt_iff]
  exact exists_firstFrozen_iff _ s.isLt

theorem D1_halts_iff : haltsFrom D1 0 ↔ ∃ n, (CryptidBoundary.run n (sourceBlank 5)).st = 6 :=
  D1_halts_from_blank.trans (raw_halts_iff 5)
theorem D2_halts_iff : haltsFrom D2 0 ↔ ∃ n, (CryptidBoundary.run n (sourceBlank 2)).st = 6 :=
  D2_halts_from_blank.trans (raw_halts_iff 2)
theorem D3_halts_iff : haltsFrom D3 0 ↔ ∃ n, (CryptidBoundary.run n (sourceBlank 1)).st = 6 :=
  D3_halts_from_blank.trans (raw_halts_iff 1)

#print axioms project_step
#print axioms project_run
#print axioms firstFrozen_gate
#print axioms firstFrozen_prefix
#print axioms raw_haltsAt_iff
#print axioms raw_halts_iff
#print axioms D1_haltsAt_iff
#print axioms D2_haltsAt_iff
#print axioms D3_haltsAt_iff
#print axioms D1_halts_iff
#print axioms D2_halts_iff
#print axioms D3_halts_iff
end BB6.BoundaryPortfolio
