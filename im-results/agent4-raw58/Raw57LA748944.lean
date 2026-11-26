import SweepPumping

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent4Raw57LA748944
open BB6Coverage Agent31Pump

inductive V where | v748 | v944 deriving DecidableEq, Repr

def table (v : V) : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,decide (v = .v944),if v = .v944 then 3 else 5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,true,2⟩)
  | _,_ => none

abbrev P : List Bool := [false,true]
abbrev P2 : List Bool := [false,true,false,true]
abbrev Q2 : List Bool := [true,false,true,false]
abbrev H : List Bool := [true,true,true]

def startCost (v : V) : Nat := if v = .v748 then 5 else 3
def leftCost (v : V) : Nat := if v = .v748 then 18 else 14
def endCost (v : V) : Nat := if v = .v748 then 17 else 13
def emptyCost1 (v : V) : Nat := if v = .v748 then 10 else 8
def emptyCost2 (v : V) : Nat := if v = .v748 then 38 else 32

def root (n : Nat) (s : List Bool) : Z0 := ⟨0,[],[true,true,false,true] ++ rep P2 n ++ s⟩

theorem init (v : V) (R : List Bool) :
    run0 (table v) (startCost v) ⟨0,[],[true,true,false] ++ R⟩ = some ⟨4,P2,R⟩ := by
  cases v <;> rfl

theorem scanOne (v : V) (L R : List Bool) :
    run0 (table v) 4 ⟨4,P2 ++ L,Q2 ++ R⟩ = some ⟨4,P2 ++ P2 ++ L,R⟩ := by
  cases v <;> rfl

theorem root_scan (v : V) (n : Nat) (s : List Bool) :
    run0 (table v) (startCost v + 4*n) (root n s) =
      some ⟨4,P2 ++ rep P2 n,[true] ++ s⟩ := by
  have h1 := init v (rep Q2 n ++ ([true] ++ s))
  have h2 := sweepR (table v) 4 P2 [] Q2 P2 4 (by intro L R; simpa using scanOne v L R) n [] ([true] ++ s)
  simp only [List.nil_append,List.append_nil] at h2
  have h := join0 h1 h2
  have hr : [true] ++ rep P2 n = rep Q2 n ++ [true] := rotate true [false,true,false] n
  have hs : [true,true,false,true] ++ rep P2 n ++ s = [true,true,false] ++ (rep Q2 n ++ ([true] ++ s)) := by
    calc
      _ = [true,true,false] ++ (([true] ++ rep P2 n) ++ s) := by simp only [List.append_assoc]; rfl
      _ = _ := by rw [hr]; simp only [List.append_assoc]
  simpa only [root,hs] using h

theorem turnMore (v : V) (L R : List Bool) :
    run0 (table v) 14 ⟨4,P ++ L,[true,true,false,true] ++ R⟩ =
      some ⟨0,L,H ++ [false,true,true] ++ R⟩ := by cases v <;> rfl

theorem turnLast (v : V) (L : List Bool) :
    run0 (table v) 14 ⟨4,P ++ L,[true,true]⟩ =
      some ⟨0,L,H ++ P⟩ := by cases v <;> rfl

theorem turnEmpty (v : V) (L : List Bool) :
    run0 (table v) 8 ⟨4,P ++ L,[true]⟩ =
      some ⟨0,P ++ L,[true,false,true]⟩ := by cases v <;> rfl

theorem leftOne (v : V) (L R : List Bool) :
    run0 (table v) (leftCost v) ⟨0,P ++ L,H ++ R⟩ =
      some ⟨0,L,H ++ P ++ R⟩ := by cases v <;> rfl

theorem leftTwo (v : V) (L R : List Bool) :
    run0 (table v) (2*leftCost v) ⟨0,P2 ++ L,H ++ R⟩ =
      some ⟨0,L,H ++ P2 ++ R⟩ := by cases v <;> rfl

theorem leftMany (v : V) (n : Nat) (R : List Bool) :
    run0 (table v) ((2*leftCost v)*n) ⟨0,rep P2 n,H ++ R⟩ =
      some ⟨0,[],H ++ rep P2 n ++ R⟩ := by
  simpa only [List.nil_append,List.append_nil] using
    sweepL (table v) 0 [] H P2 P2 (2*leftCost v)
      (by intro L R; simpa only [List.nil_append] using leftTwo v L R) n [] R

theorem endTurn (v : V) (R : List Bool) :
    run0 (table v) (endCost v) ⟨0,[],H ++ R⟩ =
      some ⟨0,[],[true,true,false,true] ++ R⟩ := by cases v <;> rfl

theorem emptyOne (v : V) (L : List Bool) :
    run0 (table v) (emptyCost1 v) ⟨0,P ++ L,[true,false,true]⟩ =
      some ⟨0,L,[true,true,false,true,true]⟩ := by cases v <;> rfl

theorem emptyTwo (v : V) (L : List Bool) :
    run0 (table v) (emptyCost2 v) ⟨0,P ++ L,[true,true,false,true,true]⟩ =
      some ⟨0,L,H ++ [true,false,true,false,true]⟩ := by cases v <;> rfl

def posCost (v : V) (n : Nat) : Nat :=
  startCost v + 4*n + 14 + leftCost v + (2*leftCost v)*n + endCost v

def zeroCost (v : V) (n : Nat) : Nat :=
  startCost v + 4*n + 8 + emptyCost1 v + emptyCost2 v + (2*leftCost v)*n + endCost v

theorem positiveMore (v : V) (n : Nat) (R : List Bool) :
    run0 (table v) (posCost v n) (root n ([true] ++ P ++ R)) =
      some (root (n+1) ([true] ++ R)) := by
  have h1 := root_scan v n ([true] ++ P ++ R)
  have h2 := turnMore v (P ++ rep P2 n) R
  have h12 := join0 h1 h2
  have h3 := leftOne v (rep P2 n) ([false,true,true] ++ R)
  have h4 := leftMany v n (P ++ [false,true,true] ++ R)
  have h1234 := join0 (join0 h12 h3) h4
  have h5 := endTurn v (rep P2 n ++ (P ++ [false,true,true] ++ R))
  have h := join0 h1234 (by simpa only [List.append_assoc] using h5)
  have hs : rep P2 (n+1) = rep P2 n ++ P2 := by
    rw [rep,rep_snoc]
  have ht : P ++ ([false,true,true] ++ R) = P2 ++ ([true] ++ R) := rfl
  simpa only [posCost,root,hs,List.append_assoc,ht] using h

theorem positiveLast (v : V) (n : Nat) :
    run0 (table v) (posCost v n) (root n [true]) = some (root (n+1) []) := by
  have h1 := root_scan v n [true]
  have h2 := turnLast v (P ++ rep P2 n)
  have h12 := join0 h1 h2
  have h3 := leftOne v (rep P2 n) P
  have h4 := leftMany v n (P ++ P)
  have h1234 := join0 (join0 h12 h3) h4
  have h5 := endTurn v (rep P2 n ++ P2)
  have h := join0 h1234 h5
  have hs : rep P2 (n+1) = rep P2 n ++ P2 := by
    rw [rep,rep_snoc]
  simpa only [posCost,root,hs,List.append_assoc,List.append_nil] using h

theorem zeroReturn (v : V) (n : Nat) :
    run0 (table v) (zeroCost v n) (root n []) = some (root n [true,false,true,false,true]) := by
  have h1 := root_scan v n []
  have h2 := turnEmpty v (P ++ rep P2 n)
  have h12 := join0 h1 h2
  have h3 := emptyOne v (P ++ rep P2 n)
  have h4 := emptyTwo v (rep P2 n)
  have h5 := leftMany v n [true,false,true,false,true]
  have h6 := endTurn v (rep P2 n ++ [true,false,true,false,true])
  have h := join0 (join0 (join0 (join0 (join0 h1 h2) h3) h4) h5) h6
  simpa only [zeroCost,root,List.append_assoc] using h

def cycleCost (v : V) (n : Nat) := posCost v n + posCost v (n+1) + posCost v (n+2) + zeroCost v (n+3)

theorem fourPhase (v : V) (n : Nat) :
    run0 (table v) (cycleCost v n) (root n [true,false,true,false,true]) =
      some (root (n+3) [true,false,true,false,true]) := by
  exact join0 (join0 (join0 (positiveMore v n [false,true]) (positiveMore v (n+1) [])) (positiveLast v (n+2))) (zeroReturn v (n+3))

theorem entry (v : V) : run0 (table v) (if v = .v748 then 87 else 73) ⟨0,[],[]⟩ = some (root 0 [true,false,true,false,true]) := by
  cases v <;> rfl

theorem never (v : V) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  let family := fun n => root (3*n) [true,false,true,false,true]
  have growth : ∀ n, run0 (table v) (cycleCost v (3*n)) (family n) = some (family (n+1)) := by
    intro n
    have h := fourPhase v (3*n)
    simpa only [family, Nat.mul_add, Nat.mul_one] using h
  exact never_of_growth (table v) family _ (fun n => cycleCost v (3*n)) (entry v)
    (by intro n; cases v <;> simp [cycleCost,posCost,zeroCost,startCost,leftCost,endCost,emptyCost1,emptyCost2] <;> omega) growth m hm

#print axioms never
end BB6Coverage.Agent4Raw57LA748944
