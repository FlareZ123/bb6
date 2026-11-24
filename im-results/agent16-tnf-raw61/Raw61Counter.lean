import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Raw61Counter
open BB6Coverage Agent31Pump
abbrev W := List Bool
abbrev o (n : Nat) : W := List.replicate n true
abbrev z (n : Nat) : W := List.replicate n false
abbrev cfg (q : Fin 6) (l r : W) : Z0 := ⟨q,l,r⟩
inductive V where | v314 | v315 | v316 | v319 | v1085
  deriving DecidableEq

def table (v : V) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨v == .v1085,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨false,true,if v == .v1085 then 5 else 0⟩)
  | 5,true => some (some (match v with
      | .v314 => ⟨false,false,0⟩
      | .v315 => ⟨false,false,4⟩
      | .v316 => ⟨false,false,5⟩
      | .v319 => ⟨true,true,3⟩
      | .v1085 => ⟨true,true,1⟩))
  | _,_ => none

def frame (v : V) : Bool := v == .v1085
def sweepCost (v : V) : Nat := if v == .v319 || v == .v1085 then 12 else 4
def E (k : Nat) (R : W) : Z0 := cfg 4 (false::true::false::true::true::(o (4*k) ++ [false])) R

theorem repTail (b : Bool) (n m : Nat) (L : W) : List.replicate n b ++ (List.replicate m b ++ L) = List.replicate (n+m) b ++ L := by
  rw [← List.append_assoc,List.replicate_append_replicate]

theorem bStep (v : V) (L R : W) :
  run0 (table v) 18 (cfg 4 (false::true::false::true::true::L) (false::false::true::false::R)) =
  some (cfg 4 (false::true::false::true::true::true::true::true::true::L) R) := by cases v <;> rfl

theorem bBlank (v : V) (L : W) :
  run0 (table v) 18 (cfg 4 (false::true::false::true::true::L) [false,false,true]) =
  some (cfg 4 (false::true::false::true::true::true::true::true::true::L) []) := by cases v <;> rfl

theorem bRule (v : V) (k : Nat) (R : W) : run0 (table v) 18 (E k (false::false::true::false::R)) = some (E (k+1) R) := by
  unfold E
  rw [show 4*(k+1)=4*k+4 by omega]
  exact bStep v (o (4*k) ++ [false]) R

theorem bRuleBlank (v : V) (k : Nat) : run0 (table v) 18 (E k [false,false,true]) = some (E (k+1) []) := by
  unfold E
  rw [show 4*(k+1)=4*k+4 by omega]
  exact bBlank v (o (4*k) ++ [false])

theorem resetPrefix (v : V) (L R : W) : run0 (table v) 23 (cfg 4 (false::true::false::true::true::L) (false::false::false::R)) = some (cfg 5 (true::true::true::true::L) (frame v::false::false::true::R)) := by cases v <;> rfl

theorem prefixBlank (v : V) (L : W) : run0 (table v) 23 (cfg 4 (false::true::false::true::true::L) []) = some (cfg 5 (true::true::true::true::L) [frame v,false,false,true]) := by cases v <;> rfl

theorem loop (v : V) (L R : W) : run0 (table v) (sweepCost v) (cfg 5 (true::true::true::true::L) (frame v::R)) = some (cfg 5 L (frame v::false::false::false::false::R)) := by cases v <;> rfl

theorem sweep (v : V) (k : Nat) (L R : W) : run0 (table v) (sweepCost v*k) (cfg 5 (o (4*k) ++ L) (frame v::R)) = some (cfg 5 L (frame v::(z (4*k) ++ R))) := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    have h := join0 (loop v (o (4*k) ++ L) R) (ih (false::false::false::false::R))
    rw [Nat.mul_succ, Nat.add_comm (sweepCost v*k) (sweepCost v)]
    rw [show 4*(k+1)=4*k+4 by omega]
    have hh : z (4*k) ++ false::false::false::false::R = z (4*k+4) ++ R := repTail false (4*k) 4 R
    rw [hh] at h
    exact h

theorem suffix (v : V) (R : W) : run0 (table v) 15 (cfg 5 [false] (frame v::false::false::false::false::false::false::R)) = some (E 0 (false::false::R)) := by cases v <;> rfl

def resetCost (v : V) (k : Nat) := 23+sweepCost v*(k+1)+15

theorem resetMid (v : V) (k : Nat) (R : W) : run0 (table v) (sweepCost v*(k+1)+15) (cfg 5 (o (4*(k+1)) ++ [false]) (frame v::false::false::true::R)) = some (E 0 (z (4*k+2) ++ true::R)) := by
  have h := sweep v (k+1) [false] (false::false::true::R)
  have hh : z (4*(k+1)) ++ false::false::true::R = z (4*k+6) ++ true::R := by
    rw [show 4*(k+1)=4*k+4 by omega,show 4*k+6=4*k+4+2 by omega]
    exact repTail false (4*k+4) 2 (true::R)
  rw [hh] at h
  have ha : z (4*k+6) ++ true::R = false::false::false::false::false::false::(z (4*k) ++ true::R) := by rfl
  rw [ha] at h
  have H := join0 h (suffix v (z (4*k) ++ true::R))
  exact H

theorem aRule (v : V) (k : Nat) (R : W) : run0 (table v) (resetCost v k) (E k (false::false::false::false::R)) = some (E 0 (z (4*k) ++ false::false::true::false::R)) := by
  have h := resetPrefix v (o (4*k) ++ [false]) (false::R)
  have h' : run0 (table v) 23 (E k (false::false::false::false::R)) = some (cfg 5 (o (4*(k+1)) ++ [false]) (frame v::false::false::true::false::R)) := by
    rw [show 4*(k+1)=4*k+4 by omega]
    exact h
  have H := join0 h' (resetMid v k (false::R))
  have hh : z (4*k+2) ++ true::false::R = z (4*k) ++ false::false::true::false::R := (repTail false (4*k) 2 (true::false::R)).symm
  rw [hh] at H
  exact H

theorem aRuleBlank (v : V) (k : Nat) : run0 (table v) (resetCost v k) (E k []) = some (E 0 (z (4*k) ++ [false,false,true])) := by
  have h := prefixBlank v (o (4*k) ++ [false])
  have h' : run0 (table v) 23 (E k []) = some (cfg 5 (o (4*(k+1)) ++ [false]) [frame v,false,false,true]) := by
    rw [show 4*(k+1)=4*k+4 by omega]
    exact h
  have H := join0 h' (resetMid v k [])
  have hh : z (4*k+2) ++ [true] = z (4*k) ++ [false,false,true] := (repTail false (4*k) 2 [true]).symm
  rw [hh] at H
  exact H

def scanCost (v : V) : Nat → Nat
  | 0 => 0
  | k+1 => scanCost v k + (resetCost v k + scanCost v k + 18)

def retCost (v : V) (k : Nat) := resetCost v k + scanCost v k + 18

theorem scan (v : V) (k : Nat) (R : W) :
  run0 (table v) (scanCost v k) (E 0 (z (4*k) ++ R)) = some (E k R) := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    have h1 := ih (false::false::false::false::R)
    have h2 := aRule v k R
    have h3 := ih (false::false::true::false::R)
    have h4 := bRule v k R
    have H := join0 h1 (join0 (join0 h2 h3) h4)
    have hh : z (4*k) ++ false::false::false::false::R = z (4*(k+1)) ++ R := by
      rw [show 4*(k+1)=4*k+4 by omega]
      exact repTail false (4*k) 4 R
    rw [hh] at H
    exact H

theorem ret (v : V) (k : Nat) (R : W) :
  run0 (table v) (retCost v k) (E k (false::false::false::false::R)) = some (E (k+1) R) :=
  join0 (join0 (aRule v k R) (scan v k (false::false::true::false::R))) (bRule v k R)

theorem retBlank (v : V) (k : Nat) :
  run0 (table v) (retCost v k) (E k []) = some (E (k+1) []) :=
  join0 (join0 (aRuleBlank v k) (scan v k [false,false,true])) (bRuleBlank v k)

theorem entry (v : V) : run0 (table v) 14 (cfg 0 [] []) = some (E 0 []) := by cases v <;> rfl

theorem retCost_succ (v : V) (k : Nat) : retCost v (k+1) = 2*retCost v k+sweepCost v := by
  unfold retCost
  simp only [scanCost,resetCost,Nat.mul_succ]
  omega

theorem retCost_formula (v : V) (k : Nat) : retCost v k+sweepCost v = (56+2*sweepCost v)*2^k := by
  induction k with
  | zero => cases v <;> rfl
  | succ k ih =>
    rw [retCost_succ,Nat.pow_succ,← Nat.mul_assoc,← ih]
    omega

theorem never (v : V) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) (fun n => E n []) 14 (retCost v) (entry v)
    (by intro n; unfold retCost; omega) (retBlank v) m hm

#print axioms retBlank
#print axioms entry
#print axioms retCost_formula
#print axioms never
end BB6Coverage.Raw61Counter

namespace BB6.Agent10Recursive
namespace R61M314
abbrev table := BB6Coverage.Raw61Counter.table .v314
theorem never (m : BB6Coverage.Machine) (hm : BB6Coverage.compatible table m) : BB6Coverage.NeverHalts m :=
  BB6Coverage.Raw61Counter.never .v314 m hm
end R61M314
namespace R61M315
abbrev table := BB6Coverage.Raw61Counter.table .v315
theorem never (m : BB6Coverage.Machine) (hm : BB6Coverage.compatible table m) : BB6Coverage.NeverHalts m :=
  BB6Coverage.Raw61Counter.never .v315 m hm
end R61M315
namespace R61M316
abbrev table := BB6Coverage.Raw61Counter.table .v316
theorem never (m : BB6Coverage.Machine) (hm : BB6Coverage.compatible table m) : BB6Coverage.NeverHalts m :=
  BB6Coverage.Raw61Counter.never .v316 m hm
end R61M316
namespace R61M319
abbrev table := BB6Coverage.Raw61Counter.table .v319
theorem never (m : BB6Coverage.Machine) (hm : BB6Coverage.compatible table m) : BB6Coverage.NeverHalts m :=
  BB6Coverage.Raw61Counter.never .v319 m hm
end R61M319
namespace R61M1085
abbrev table := BB6Coverage.Raw61Counter.table .v1085
theorem never (m : BB6Coverage.Machine) (hm : BB6Coverage.compatible table m) : BB6Coverage.NeverHalts m :=
  BB6Coverage.Raw61Counter.never .v1085 m hm
end R61M1085
end BB6.Agent10Recursive
