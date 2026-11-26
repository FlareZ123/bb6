import Box33BinaryCounter

namespace BB6.Agent13.Box33UnarySweeper
open C9Pair
open BB6.Agent13.Box33BinaryCounter (zeros zero_head zero_pop zero_push rep ones ones_succ)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def step (c : Config) : Option Config :=
  match c.q, c.a with
  | .A, false => some (right .B true c)
  | .A, true => some (right .F true c)
  | .B, false => some (left .C true c)
  | .B, true => some (left .D false c)
  | .C, false => some (left .A false c)
  | .C, true => some (left .D false c)
  | .D, false => some (right .A false c)
  | .D, true => some (left .F true c)
  | .E, false => none
  | .E, true => some (right .C false c)
  | .F, false => some (right .A true c)
  | .F, true => some (right .E true c)

def run : Nat → Config → Option Config
  | 0, c => some c
  | n+1, c => (step c).bind (run n)

theorem run_add (m n : Nat) (c : Config) :
    run (m+n) c = (run m c).bind (run n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih =>
    rw [Nat.succ_add]; simp only [run]
    cases h : step c <;> simp [ih]

def phaseR (m r : Nat) : Config := ⟨.E,ones m,true,ones r⟩
def phaseL (m r : Nat) : Config := ⟨.E,ones m,true,push false (ones r)⟩

theorem leftStep (m r : Nat) : run 7 (phaseL (m+2) r) = some (phaseL (m+1) (r+1)) := by
  simp [phaseL,run,step,left,right]

theorem turn (r : Nat) : run 11 (phaseL 1 (r+2)) = some (phaseR 5 r) := by
  simp [phaseL,phaseR,run,step,left,right,ones,rep]

theorem rightStep (m r : Nat) : run 11 (phaseR m (r+5)) = some (phaseR (m+5) r) := by
  simp [phaseR,run,step,left,right]

theorem rightEndTwo (m : Nat) : run 14 (phaseR m 2) = some (phaseL (m+2) 1) := by
  simp [phaseR,phaseL,run,step,left,right,ones,rep]

theorem rightEndZero (m : Nat) : phaseR m 0 = phaseL m 0 := by
  simp [phaseR,phaseL,ones,rep]

/-- Sweep all but one left-hand one, while shifting the gap to the left. -/
theorem leftSweep (n r : Nat) : run (7*n) (phaseL (n+1) r) = some (phaseL 1 (r+n)) := by
  induction n generalizing r with
  | zero => simp [run]
  | succ n ih =>
    rw [show 7*(n+1) = 7+7*n by omega,run_add,leftStep,Option.bind_some,ih]
    rw [show r+1+n = r+(n+1) by omega]

/-- Sweep through k rightward five-cell blocks. -/
theorem rightSweep (k m r : Nat) : run (11*k) (phaseR m (5*k+r)) = some (phaseR (m+5*k) r) := by
  induction k generalizing m with
  | zero => simp [run]
  | succ k ih =>
    rw [show 11*(k+1) = 11+11*k by omega,show 5*(k+1)+r = (5*k+r)+5 by omega,
      run_add,rightStep,Option.bind_some,ih]
    rw [show m+5+5*k = m+5*(k+1) by omega]

def root (k : Nat) (b : Bool) : Config := phaseR 5 (5*k + if b then 2 else 0)

theorem progress (k : Nat) (b : Bool) : ∃ n k' b', 0 < n ∧ run n (root k b) = some (root k' b') := by
  cases b with
  | false =>
    refine ⟨11*k + 7*(4+5*k) + 11,k,true,by omega,?_⟩
    rw [root, if_neg (by decide : false ≠ true), run_add, run_add]
    rw [show 5*k+0 = 5*k+0 by rfl,rightSweep,Option.bind_some,rightEndZero]
    rw [show 5+5*k = (4+5*k)+1 by omega,leftSweep,Option.bind_some]
    rw [show 0+(4+5*k) = (5*k+2)+2 by omega,turn]
    rfl
  | true =>
    refine ⟨11*k+14+7*(6+5*k)+11,k+1,false,by omega,?_⟩
    rw [root,if_pos rfl,run_add,run_add,run_add,rightSweep,Option.bind_some,rightEndTwo,Option.bind_some]
    rw [show 5+5*k+2 = (6+5*k)+1 by omega,leftSweep,Option.bind_some]
    rw [show 1+(6+5*k) = (5*(k+1))+2 by omega,turn]
    simp [root]

theorem never_root (n k : Nat) (b : Bool) : run n (root k b) ≠ none := by
  induction n using Nat.strongRecOn generalizing k b with
  | ind n ih =>
    intro h
    obtain ⟨t,k',b',ht,hr⟩ := progress k b
    by_cases hnt : n ≤ t
    · have he : n+(t-n) = t := by omega
      rw [←he,run_add,h] at hr
      contradiction
    · have he : t+(n-t) = n := by omega
      rw [←he,run_add,hr,Option.bind_some] at h
      exact ih (n-t) (by omega) k' b' h

def blank : Config := ⟨.A,zeros,false,zeros⟩

theorem init : run 33 blank = some (root 0 false) := by
  have h10 : run 10 blank = some ⟨.A,ones 3,false,zeros⟩ := by
    simp [blank,run,step,right,left,ones,rep]
  have h5 : run 5 ⟨.A,ones 3,false,zeros⟩ = some (phaseL 2 1) := by
    simp [phaseL,run,step,right,left,ones,rep]
  rw [show 33 = 10+5+7+11 by decide,run_add,run_add,run_add,h10,Option.bind_some,h5,Option.bind_some]
  rw [leftStep 0 1,Option.bind_some,turn 0]
  rfl

theorem never_blank (n : Nat) : run n blank ≠ none := by
  intro h
  by_cases hn : n ≤ 33
  · have he : n+(33-n) = 33 := by omega
    have hh := init
    rw [←he,run_add,h] at hh
    contradiction
  · have he : 33+(n-33) = n := by omega
    rw [←he,run_add,init,Option.bind_some] at h
    exact never_root (n-33) 0 false h

#print axioms never_blank
end BB6.Agent13.Box33UnarySweeper
