import SweepPumping
set_option maxRecDepth 100000
namespace BB6.Agent10Raw91Pump
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun (q,b) =>
  match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some ⟨true,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true  => some (some ⟨true,true,4⟩)
  | 4,false => none
  | 4,true  => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true  => some (some ⟨false,true,2⟩)
  | _,_ => none

abbrev ones (n : Nat) : List Bool := List.replicate n true
theorem ones_add (n m : Nat) : ones n ++ ones m = ones (n+m) := List.replicate_append_replicate

abbrev F (l r : List Bool) : Z0 := ⟨5,l,r⟩

def family (n : Nat) : Z0 := F [] ([true,false] ++ ones (5*n+5))

theorem first : run0 table 56 ⟨0,[],[]⟩ = some (family 0) := by decide

theorem enter (R : List Bool) :
    run0 table 4 (F [] ([true,false,true,true] ++ R)) = some (F (ones 5) R) := by rfl

theorem right_one (L R : List Bool) :
    run0 table 11 (F (true::L) (ones 5 ++ R)) = some (F (true::(ones 5 ++ L)) R) := by rfl

theorem right_many (n : Nat) (l r : Nat) :
    run0 table (11*n) (F (true::ones l) (ones (5*n+r))) =
      some (F (true::ones (5*n+l)) (ones r)) := by
  induction n generalizing l with
  | zero => simp [run0]
  | succ n ih =>
    have h := right_one (ones l) (ones (5*n+r))
    simp only [ones_add] at h
    have h' := ih (5+l)
    have H := join0 h h'
    rw [show 11*(n+1)=11+11*n by omega, show 5*(n+1)+r=5+(5*n+r) by omega, show 5*(n+1)+l=5*n+(5+l) by omega]
    exact H

theorem turn (L : List Bool) :
    run0 table 18 (F (true::L) (ones 3)) = some (F (ones 5 ++ L) [true,false,true]) := by rfl

theorem left_one (L R : List Bool) :
    run0 table 9 (F (true::true::L) ([true,false] ++ R)) =
      some (F (true::L) ([true,false,true] ++ R)) := by rfl

theorem left_many (n r : Nat) :
    run0 table (9*n) (F (true::ones n) ([true,false] ++ ones r)) =
      some (F [true] ([true,false] ++ ones (n+r))) := by
  induction n generalizing r with
  | zero => simp [run0]
  | succ n ih =>
    have h := left_one (ones n) (ones r)
    have h' : run0 table 9 (F (true::ones (n+1)) ([true,false] ++ ones r)) =
      some (F (true::ones n) ([true,false] ++ ones (r+1))) := by
      simpa [List.replicate_succ, List.replicate_succ', Nat.add_comm] using h
    have H := join0 h' (ih (r+1))
    rw [show 9*(n+1)=9+9*n by omega, show n+1+r=n+(r+1) by omega]
    exact H

theorem leave (R : List Bool) :
    run0 table 9 (F [true] ([true,false] ++ R)) = some (F [] ([true,false,true] ++ R)) := by rfl

theorem growth (n : Nat) :
    run0 table (56*n+103) (family n) = some (family (n+1)) := by
  have h0 := enter (ones (5*n+3))
  have h1 := right_many n 4 3
  have h2 := turn (ones (5*n+4))
  have h3 := left_many (5*n+8) 1
  have h4 := leave (ones (5*n+9))
  have H0 : run0 table 4 (family n) = some (F (true::ones 4) (ones (5*n+3))) := by
    unfold family
    rw [show 5*n+5=2+(5*n+3) by omega, ← ones_add 2 (5*n+3)]
    exact h0
  have H2 : run0 table 18 (F (true::ones (5*n+4)) (ones 3)) =
      some (F (true::ones (5*n+8)) ([true,false] ++ ones 1)) := by
    rw [show 5*n+8=4+(5*n+4) by omega, ← ones_add 4 (5*n+4)]
    exact h2
  have H := join0 (join0 (join0 (join0 H0 h1) H2) h3) h4
  rw [show 56*n+103=4+11*n+18+9*(5*n+8)+9 by omega]
  unfold family at H ⊢
  rw [show 5*(n+1)+5=1+(5*n+9) by omega, ← ones_add 1 (5*n+9)]
  exact H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 56 (fun n => 56*n+103) first (by intro n; omega) growth m hm

#print axioms first
#print axioms growth
#print axioms never
end BB6.Agent10Raw91Pump
