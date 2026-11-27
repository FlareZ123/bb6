import SweepPumping
import FastFAR

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13Coupled5Hard0LC
open BB6Coverage BB6Coverage.Agent31Pump

/-- Literal residual 1RB1LD1RC1RA1LA1RE0LC0LA0RF0RD---1RC. -/
def p : PartialMachine := FAR.fromCodes [7,14,11,3,2,19,8,0,21,13,24,11]
abbrev X : List Bool := [true,false]
abbrev Y : List Bool := [false,true]
abbrev U : List Bool := [true,true]
abbrev Fleft : List Bool := [true,false,true,true,true]

theorem rep_add (P : List Bool) (a b : Nat) :
    rep P (a+b) = rep P a ++ rep P b := by
  induction a with
  | zero => simp [rep]
  | succ a ih =>
    rw [Nat.succ_add,rep,ih,rep]
    simp only [List.append_assoc]

theorem rep_tail (P : List Bool) (n : Nat) :
    rep P (n+1) = rep P n ++ P := (rep_snoc P n).symm

theorem rot (n : Nat) : [true] ++ rep Y n = rep X n ++ [true] := by
  simpa using rotate true [false] n

theorem rotU (n : Nat) : [true] ++ rep U n = rep U n ++ [true] := by
  simpa using rotate true [true] n

theorem entry101 (R : List Bool) :
    run0 p 101 ⟨5,Fleft,rep Y 4 ++ R⟩ =
      some ⟨0,[],rep X 9 ++ ([true] ++ R)⟩ := by rfl

theorem startR (R : List Bool) :
    run0 p 2 ⟨0,[],X++R⟩ = some ⟨0,[false]++U,R⟩ := by rfl

theorem rPair (L R : List Bool) :
    run0 p 2 ⟨0,[false]++L,[]++X++R⟩ =
      some ⟨0,[false]++U++L,[]++R⟩ := by rfl

theorem lPair (L R : List Bool) :
    run0 p 2 ⟨0,[]++U++L,[]++R⟩ =
      some ⟨0,[]++L,[]++Y++R⟩ := by rfl

theorem bulkRight (k : Nat) (R : List Bool) :
    run0 p (2*(k+1)) ⟨0,[],rep X (k+1)++R⟩ =
      some ⟨0,[false]++rep U (k+1),R⟩ := by
  have a : run0 p 2 ⟨0,[],rep X (k+1)++R⟩ =
      some ⟨0,[false]++U,rep X k++R⟩ := by
    simpa only [rep,List.append_assoc] using startR (rep X k++R)
  have b : run0 p (2*k) ⟨0,[false]++U,rep X k++R⟩ =
      some ⟨0,[false]++rep U (k+1),R⟩ := by
    rw [rep_tail U k]
    simpa only [List.nil_append,List.append_assoc] using
      sweepR p 0 [false] [] X U 2 rPair k U R
  simpa only [show 2+2*k=2*(k+1) by omega] using join0 a b

theorem rEnd11 (L : List Bool) :
    run0 p 2 ⟨0,[false]++L,U⟩ = some ⟨0,[true,true,true]++L,[]⟩ := by rfl

theorem rEnd1 (L : List Bool) :
    run0 p 2 ⟨0,[false]++L,[true]⟩ = some ⟨0,[false,true,true]++L,[]⟩ := by rfl

theorem ones_end (k : Nat) :
    [true,true,true] ++ rep U k = rep U (k+1) ++ [true] := by
  change U ++ ([true] ++ rep U k) = _
  rw [rotU]
  simp only [rep,List.append_assoc]

theorem right11 (k : Nat) :
    run0 p (2*(k+2)) ⟨0,[],rep X (k+1)++U⟩ =
      some ⟨0,rep U (k+2)++[true],[]⟩ := by
  have h := join0 (bulkRight k U) (rEnd11 (rep U (k+1)))
  simpa only [ones_end,show 2*(k+1)+2=2*(k+2) by omega] using h

theorem right1 (k : Nat) :
    run0 p (2*(k+2)) ⟨0,[],rep X (k+1)++[true]⟩ =
      some ⟨0,[false]++rep U (k+2),[]⟩ := by
  have h := join0 (bulkRight k [true]) (rEnd1 (rep U (k+1)))
  have w : [false,true,true]++rep U (k+1) = [false]++rep U (k+2) := by
    rw [show rep U (k+2) = U++rep U (k+1) by rfl] <;> rfl
  simpa only [w,show 2*(k+1)+2=2*(k+2) by omega] using h

theorem leftSweep (k : Nat) (L R : List Bool) :
    run0 p (2*k) ⟨0,rep U k++L,R⟩ =
      some ⟨0,L,rep Y k++R⟩ := by
  simpa only [List.nil_append] using sweepL p 0 [] [] U Y 2 lPair k L R

theorem turnLeft (R : List Bool) :
    run0 p 3 ⟨0,[true],R⟩ = some ⟨0,[],[true,false,true]++R⟩ := by rfl

theorem left_to_right (k : Nat) :
    run0 p 3 ⟨0,[true],rep Y k⟩ =
      some ⟨0,[],rep X (k+1)++[true]⟩ := by
  have w : [true,false,true]++rep Y k = rep X (k+1)++[true] := by
    change X++([true]++rep Y k) = _
    rw [rot]
    simp only [rep,List.append_assoc]
  simpa only [w] using turnLeft (rep Y k)

theorem turnRight (k : Nat) :
    run0 p 3 ⟨0,[false]++rep U k,[]⟩ =
      some ⟨0,rep U (k+1),[true]⟩ := by rfl

theorem finish (R : List Bool) :
    run0 p 4 ⟨0,[],rep Y 2++R⟩ = some ⟨5,Fleft,R⟩ := by rfl

def fam (n : Nat) : Z0 := ⟨5,Fleft,rep Y (n+4)++[true]⟩

theorem entry (n : Nat) :
    run0 p 101 (fam n) = some ⟨0,[],rep X (n+9)++U⟩ := by
  have a : rep Y (n+4)++[true] = rep Y 4++(rep Y n++[true]) := by
    rw [Nat.add_comm n 4,rep_add,List.append_assoc]
  have b : rep X 9++([true]++(rep Y n++[true])) = rep X (n+9)++U := by
    rw [← List.append_assoc [true] (rep Y n) [true],rot]
    rw [List.append_assoc,← List.append_assoc (rep X 9) (rep X n),← rep_add,Nat.add_comm 9 n] <;> rfl
  rw [fam,a,←b]
  exact entry101 (rep Y n++[true])

theorem advance (n : Nat) :
    run0 p (201+8*n) (fam n) = some (fam (n+7)) := by
  have h0 := entry n
  have h1 := right11 (n+8)
  have h2 : run0 p (2*(n+10)) ⟨0,rep U (n+10)++[true],[]⟩ =
      some ⟨0,[true],rep Y (n+10)⟩ := by
    simpa only [List.append_nil] using leftSweep (n+10) [true] []
  have h3 := left_to_right (n+10)
  have h4 := right1 (n+10)
  have h5 := turnRight (n+12)
  have h6 : run0 p (2*(n+13)) ⟨0,rep U (n+13),[true]⟩ =
      some ⟨0,[],rep Y (n+13)++[true]⟩ := by
    simpa only [List.append_nil] using leftSweep (n+13) [] [true]
  have h7 : run0 p 4 ⟨0,[],rep Y (n+13)++[true]⟩ = some (fam (n+7)) := by
    have w : rep Y (n+13)++[true] = rep Y 2++(rep Y (n+11)++[true]) := by
      rw [show n+13=2+(n+11) by omega,rep_add,List.append_assoc]
    rw [w]
    exact finish (rep Y (n+11)++[true])
  have h := join0 (join0 (join0 (join0 (join0 (join0 (join0 h0 h1) h2) h3) h4) h5) h6) h7
  simpa only [show 101+2*(n+8+2)+2*(n+10)+3+2*(n+10+2)+3+2*(n+13)+4=201+8*n by omega] using h

theorem seed : run0 p 60 ⟨0,[],[]⟩ = some (fam 0) := by rfl

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
  apply never_of_growth p (fun k => fam (7*k)) 60 (fun k => 201+56*k) seed
  · intro k; omega
  · intro k
    have h := advance (7*k)
    simpa only [show 201+8*(7*k)=201+56*k by omega,show 7*k+7=7*(k+1) by omega] using h
  · exact hm

#print axioms advance
#print axioms never
end BB6.Agent46Raw13Coupled5Hard0LC
