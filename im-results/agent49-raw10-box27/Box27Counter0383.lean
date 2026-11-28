import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Counter0383
open BB6Coverage

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,4⟩)
  | 1,false => some (some ⟨true,false,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,false,3⟩)
  | 2,true => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,5⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none

def P : List Bool := [false,true]
def Q : List Bool := [true,false]
def U : List Bool := [true,true]

theorem firstStep (R : List Bool) : run0 table 1 ⟨5,[false],Q++R⟩ = some ⟨0,Q,[false]++R⟩ := by rfl

theorem rightAtom (L R : List Bool) :
    run0 table 2 ⟨0,[true]++L,[false]++Q++R⟩ = some ⟨0,[true]++U++L,[false]++R⟩ := by rfl

theorem turnInner (L R : List Bool) :
    run0 table 4 ⟨0,[true]++L,[false]++P++R⟩ = some ⟨3,[true,true,true]++L,[false]++R⟩ := by rfl

theorem leftInnerAtom (L R : List Bool) :
    run0 table 2 ⟨3,[true,true,true]++U++L,[false]++R⟩ = some ⟨3,[true,true,true]++L,[false]++Q++R⟩ := by rfl

theorem innerFinish (R : List Bool) :
    run0 table 3 ⟨3,[true,true,true,false],[false]++R⟩ = some ⟨5,[false],Q++Q++R⟩ := by rfl

theorem inner (n : Nat) (R : List Bool) :
    run0 table (8+4*n) ⟨5,[false],Q++rep Q n++P++R⟩ = some ⟨5,[false],Q++Q++rep Q n++R⟩ := by
  have a := firstStep (rep Q n++P++R)
  have b := sweepR table 0 [true] [false] Q U 2 rightAtom n [false] (P++R)
  have c := turnInner (rep U n++[false]) R
  have d := sweepL table 3 [true,true,true] [false] U Q 2 leftInnerAtom n [false] R
  have e := innerFinish (rep Q n++R)
  have a' : run0 table 1 ⟨5,[false],Q++rep Q n++P++R⟩ = some ⟨0,[true]++[false],[false]++rep Q n++(P++R)⟩ := by simpa only [List.cons_append,List.nil_append,Q,List.append_assoc] using a
  have b' : run0 table (2*n) ⟨0,[true]++[false],[false]++rep Q n++(P++R)⟩ = some ⟨0,[true]++(rep U n++[false]),[false]++P++R⟩ := by simpa only [List.cons_append,List.nil_append,List.append_assoc] using b
  have c' : run0 table 4 ⟨0,[true]++(rep U n++[false]),[false]++P++R⟩ = some ⟨3,[true,true,true]++rep U n++[false],[false]++R⟩ := by simpa only [List.cons_append,List.nil_append,List.append_assoc] using c
  have d' : run0 table (2*n) ⟨3,[true,true,true]++rep U n++[false],[false]++R⟩ = some ⟨3,[true,true,true,false],[false]++(rep Q n++R)⟩ := by simpa only [List.cons_append,List.nil_append,List.append_assoc] using d
  have H := join0 (join0 (join0 (join0 a' b') c') d') e
  rw [show 1+2*n+4+2*n+3 = 8+4*n by omega] at H
  simpa only [List.cons_append,List.nil_append,List.append_assoc] using H

theorem turnOuter (L : List Bool) :
    run0 table 5 ⟨0,[true]++L,[false]⟩ = some ⟨3,[true,true]++L,P⟩ := by rfl

theorem leftOuterAtom (L R : List Bool) :
    run0 table 2 ⟨3,[true,true]++U++L,P++R⟩ = some ⟨3,[true,true]++L,P++P++R⟩ := by rfl

theorem outerFinish (R : List Bool) :
    run0 table 14 ⟨3,[true,true,false],P++R⟩ = some ⟨5,[false],Q++Q++P++R⟩ := by rfl

theorem outer (n : Nat) :
    run0 table (20+4*n) ⟨5,[false],Q++rep Q n⟩ = some ⟨5,[false],Q++Q++P++rep P n⟩ := by
  have a := firstStep (rep Q n)
  have b := sweepR table 0 [true] [false] Q U 2 rightAtom n [false] []
  have c := turnOuter (rep U n++[false])
  have d := sweepL table 3 [true,true] P U P 2 leftOuterAtom n [false] []
  have e := outerFinish (rep P n)
  have a' : run0 table 1 ⟨5,[false],Q++rep Q n⟩ = some ⟨0,[true]++[false],[false]++rep Q n⟩ := by simpa only [List.cons_append,List.nil_append,Q] using a
  have b' : run0 table (2*n) ⟨0,[true]++[false],[false]++rep Q n⟩ = some ⟨0,[true]++(rep U n++[false]),[false]⟩ := by simpa only [List.cons_append,List.nil_append,List.append_assoc,List.append_nil] using b
  have c' : run0 table 5 ⟨0,[true]++(rep U n++[false]),[false]⟩ = some ⟨3,[true,true]++rep U n++[false],P⟩ := by simpa only [List.cons_append,List.nil_append,List.append_assoc] using c
  have d' : run0 table (2*n) ⟨3,[true,true]++rep U n++[false],P⟩ = some ⟨3,[true,true,false],P++rep P n⟩ := by simpa only [List.cons_append,List.nil_append,List.append_assoc,List.append_nil] using d
  have H := join0 (join0 (join0 (join0 a' b') c') d') e
  rw [show 1+2*n+5+2*n+14 = 20+4*n by omega] at H
  simpa only [List.cons_append,List.nil_append,List.append_assoc] using H

def walkCost (n : Nat) : Nat → Nat
  | 0 => 0
  | j+1 => 8+4*n+walkCost (n+1) j

theorem walk (n j : Nat) :
    run0 table (walkCost n j) ⟨5,[false],rep Q (n+1)++rep P j⟩ = some ⟨5,[false],rep Q (n+j+1)⟩ := by
  induction j generalizing n with
  | zero => simp [walkCost,rep,run0]
  | succ j ih =>
    have h1 : run0 table (8+4*n) ⟨5,[false],rep Q (n+1)++rep P (j+1)⟩ = some ⟨5,[false],rep Q (n+1+1)++rep P j⟩ := by
      simpa only [List.cons_append,List.nil_append,rep,List.append_assoc] using inner n (rep P j)
    have H := join0 h1 (ih (n+1))
    simpa only [List.cons_append,List.nil_append,walkCost,show n+1+j+1=n+(j+1)+1 by omega] using H

def family (k : Nat) : Z0 := ⟨5,[false],rep Q (2*k+2)⟩
def cost (k : Nat) : Nat := 20+4*(2*k+1)+walkCost 1 (2*k+2)

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (k : Nat) : run0 table (cost k) (family k) = some (family (k+1)) := by
  have h1 : run0 table (20+4*(2*k+1)) (family k) = some ⟨5,[false],rep Q 2++rep P (2*k+2)⟩ := by
    simpa only [List.cons_append,List.nil_append,family,rep,List.append_assoc,show 2*k+2=2*k+1+1 by omega] using outer (2*k+1)
  have H := join0 h1 (walk 1 (2*k+2))
  simpa only [List.cons_append,List.nil_append,cost,family,show 1+(2*k+2)+1=2*(k+1)+2 by omega] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 15 cost entry (by intro k; unfold cost; omega) growth m hm
#print axioms never
end BB6Coverage.Agent31Pump.Counter0383
