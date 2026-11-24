import SweepPumping

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47Raw83Pump
open BB6Coverage BB6Coverage.Agent31Pump

/-- The one-hole raw83 sibling leaf: E0 is the sole unassigned row. -/
def table : PartialMachine := fun (q,b) =>
  match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true  => some (some ⟨true,true,4⟩)
  | 4,false => none
  | 4,true  => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true  => some (some ⟨false,true,0⟩)
  | _,_ => none

abbrev ones (n : Nat) : List Bool := List.replicate n true

theorem ones_add (n m : Nat) : ones n ++ ones m = ones (n+m) :=
  List.replicate_append_replicate

abbrev F (l r : List Bool) : Z0 := ⟨1,l,r⟩
abbrev E (l r : List Bool) : Z0 := ⟨4,l,r⟩

/-- The nth renewal state has two blank markers around the head and 2n
    additional ones on its right ray. -/
def family (n : Nat) : Z0 :=
  F [true,false,true,true] ([false] ++ ones (2*n))

/-- After the marker pair sweeps across the right ray, its 2n ones have
    been transferred to the left ray. -/
def endState (n : Nat) : Z0 :=
  F ([true,false,true,true] ++ ones (2*n)) [false]

theorem first : run0 table 24 ⟨0,[],[]⟩ = some (family 0) := by decide

/-- Eight steps transfer a two-one block from the right ray to the left. -/
theorem shift_one (L R : List Bool) :
    run0 table 8 (F ([true,false,true,true] ++ L) ([false,true,true] ++ R)) =
      some (F ([true,false,true,true,true,true] ++ L) ([false] ++ R)) := by
  rfl

theorem rep_pair (n : Nat) : rep [true,true] n = ones (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      rep [true,true] (n+1) = [true,true] ++ rep [true,true] n := rfl
      _ = ones 2 ++ ones (2*n) := by rw [ih]; rfl
      _ = ones (2+2*n) := ones_add 2 (2*n)
      _ = ones (2*(n+1)) := by congr 1 <;> omega

theorem shift_many (n : Nat) :
    run0 table (8*n) (family n) = some (endState n) := by
  have h := sweepR table 1 [true,false,true,true] [false]
    [true,true] [true,true] 8 shift_one n [] []
  simpa [family,endState,rep_pair] using h

/-- Nine steps enter the E-state sweep after the two blank markers have
    reached the required position. -/
theorem enter (L : List Bool) :
    run0 table 9 (F ([true,false,true,true,true,true] ++ L) [false]) =
      some (E ([true] ++ ones 6 ++ L) [true]) := by
  rfl

/-- A nine-step E-sweep consumes one left-ray one and emits one right-ray one. -/
theorem left_one (L R : List Bool) :
    run0 table 9 (E (ones 3 ++ L) (true::R)) =
      some (E (ones 2 ++ L) (ones 2 ++ R)) := by
  rfl

theorem left_many (n r : Nat) (hr : 1 ≤ r) :
    run0 table (9*n) (E (ones (n+2)) (ones r)) =
      some (E (ones 2) (ones (r+n))) := by
  induction n generalizing r with
  | zero =>
      simp [run0]
  | succ n ih =>
      cases r with
      | zero => omega
      | succ r =>
          have h := left_one (ones n) (ones r)
          have h' : run0 table 9 (E (ones (n+3)) (ones (r+1))) =
              some (E (ones (n+2)) (ones (r+2))) := by
            have hL : ones (n+3) = ones 3 ++ ones n := by
              rw [ones_add]
              congr 1 <;> omega
            have hR : ones (r+1) = true::ones r := by
              simp [ones]
            have hL' : ones (n+2) = ones 2 ++ ones n := by
              rw [ones_add]
              congr 1 <;> omega
            have hR' : ones (r+2) = ones 2 ++ ones r := by
              rw [ones_add]
              congr 1 <;> omega
            rw [hL,hR,hL',hR']
            exact h
          have H := join0 h' (ih (r+2) (by omega))
          rw [show 9*(n+1) = 9+9*n by omega,
              show (r+2)+n = (r+1)+(n+1) by omega]
          exact H

/-- The final nine steps restore the raw83 renewal shape. -/
theorem leave (R : List Bool) :
    run0 table 9 (E (ones 2) (ones 4 ++ R)) =
      some (F [true,false,true,true] ([false,true,true] ++ R)) := by
  rfl

/-- Exact quadratic-time renewal: one epoch costs 26n+45 steps. -/
theorem growth (n : Nat) :
    run0 table (26*n+45) (family n) = some (family (n+1)) := by
  cases n with
  | zero =>
      decide
  | succ n =>
      have h0 := shift_many (n+1)
      have h1 : run0 table 9 (endState (n+1)) =
          some (E (ones (2*n+7)) [true]) := by
        unfold endState
        have hs : ones (2*(n+1)) = ones 2 ++ ones (2*n) := by
          rw [ones_add]
          congr 1 <;> omega
        rw [hs]
        simpa [F,E,ones_add,List.append_assoc,Nat.add_comm,
          Nat.add_left_comm,Nat.add_assoc] using enter (ones (2*n))
      have h2 := left_many (2*n+5) 1 (by omega)
      have h2' : run0 table (9*(2*n+5))
          (E (ones (2*n+7)) [true]) =
          some (E (ones 2) (ones (2*n+6))) := by
        simpa [show (2*n+5)+2 = 2*n+7 by omega,
          show 1+(2*n+5) = 2*n+6 by omega] using h2
      have h3 : run0 table 9 (E (ones 2) (ones (2*n+6))) =
          some (family (n+2)) := by
        have h := leave (ones (2*n+2))
        have hs : 2*n+6 = 4+(2*n+2) := by omega
        rw [hs, ← ones_add 4 (2*n+2)]
        simpa [family,show 2*(n+2)=2*n+4 by omega,
          ones_add,List.append_assoc,Nat.add_comm,
          Nat.add_left_comm,Nat.add_assoc] using h
      have H := join0 (join0 (join0 h0 h1) h2') h3
      rw [show 26*(n+1)+45 = (8*(n+1)+9+9*(2*n+5))+9 by omega]
      simpa [family,endState] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 24 (fun n => 26*n+45) first
    (by intro n; omega) growth m hm

#print axioms first
#print axioms growth
#print axioms never

end BB6.Agent47Raw83Pump
