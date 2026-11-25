import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent6Raw57RB1Pumps.M240
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

abbrev ZZZ : List Bool := [false,false,false]
abbrev OZZ : List Bool := [true,false,false]
abbrev TTT : List Bool := [true,true,true]

def a (b : Bool) (L R : List Bool) : Z0 := ⟨0,b::L,ZZZ++R⟩
def sec (R : List Bool) := a false [false] R

theorem carryAtom (b : Bool) (L R : List Bool) :
    run0 table 11 (a b L (OZZ++R)) = some (a true (TTT++L) R) := by
  cases b <;> rfl

theorem carry (k : Nat) (b : Bool) (L R : List Bool) :
    run0 table (11*k) (a b L (rep OZZ k++R)) =
      some (a (if k=0 then b else true) (rep TTT k++L) R) := by
  induction k generalizing b L with
  | zero => rfl
  | succ k ih =>
    have h := join0 (carryAtom b L (rep OZZ k++R)) (ih true (TTT++L))
    rw [show 11*(k+1)=11+11*k by omega]
    simp only [ite_self, Nat.succ_ne_zero, ite_false] at h ⊢
    simpa only [rep,List.append_assoc,← List.append_assoc (rep TTT k) TTT L,rep_snoc TTT k] using h

theorem incAtom (b : Bool) (L R : List Bool) :
    run0 table 11 (a b L (ZZZ++R)) =
      some ⟨5,[true,true,true,true]++L,OZZ++R⟩ := by cases b <;> rfl

theorem overflowAtom (b : Bool) (L : List Bool) :
    run0 table 22 (a b L [true]) =
      some ⟨5,[true,true,true,true,true,true,true]++L,[true]⟩ := by cases b <;> rfl

theorem fAtom (L R : List Bool) :
    run0 table 3 ⟨5,TTT++L,R⟩ = some ⟨5,L,ZZZ++R⟩ := by rfl

theorem fSweep (k : Nat) (R : List Bool) :
    run0 table (3*k) ⟨5,rep TTT k++[false],R⟩ = some ⟨5,[false],rep ZZZ k++R⟩ := by
  simpa using sweepL table 5 [] [] TTT ZZZ 3 fAtom k [false] R

theorem four (L R : List Bool) :
    run0 table 4 ⟨5,[true,true,true,true]++L,R⟩ = some ⟨5,L,[false,false,false,false]++R⟩ := by rfl

theorem seven (L R : List Bool) :
    run0 table 7 ⟨5,[true,true,true,true,true,true,true]++L,R⟩ = some ⟨5,L,[false,false,false,false,false,false,false]++R⟩ := by rfl

theorem zerosCommute (k : Nat) : [false]++rep ZZZ k = rep ZZZ k++[false] := by
  exact rotate false [false,false] k

theorem finish (k : Nat) (R : List Bool) :
    run0 table 1 ⟨5,[false],rep ZZZ k++[false,false,false,false]++R⟩ =
      some (sec (rep ZZZ k++R)) := by
  have h : rep ZZZ k++[false,false,false,false]++R = [false]++ZZZ++rep ZZZ k++R := by
    calc
      _ = (rep ZZZ k++[false])++ZZZ++R := by simp only [List.append_assoc]; rfl
      _ = _ := by rw [← zerosCommute k]; simp only [List.append_assoc,rep_snoc ZZZ k]
  rw [h]
  rfl

theorem increment (k : Nat) (R : List Bool) :
    run0 table (14*k+16) (sec (rep OZZ k++ZZZ++R)) =
      some (sec (rep ZZZ k++OZZ++R)) := by
  have h1 := carry k false [false] (ZZZ++R)
  have h2 := incAtom (if k=0 then false else true) (rep TTT k++[false]) R
  have h3 := four (rep TTT k++[false]) (OZZ++R)
  have h4 := fSweep k ([false,false,false,false]++OZZ++R)
  have h5 := finish k (OZZ++R)
  simp only [List.append_assoc] at h1 h2 h3 h4 h5
  have h := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  rw [show 14*k+16=11*k+11+4+3*k+1 by omega]
  simpa only [sec,List.append_assoc] using h

theorem overflow (k : Nat) :
    run0 table (14*k+30) (sec (rep OZZ k++[true])) =
      some (sec (rep ZZZ (k+1)++[true])) := by
  have h1 := carry k false [false] [true]
  have h2 := overflowAtom (if k=0 then false else true) (rep TTT k++[false])
  have h3 := seven (rep TTT k++[false]) [true]
  have h4 := fSweep k ([false,false,false,false,false,false,false,true])
  have h5 := finish k (ZZZ++[true])
  simp only [List.append_assoc] at h1 h2 h3 h4 h5
  have h := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  rw [show 14*k+30=11*k+22+7+3*k+1 by omega]
  simpa only [sec,rep,List.append_assoc,← List.append_assoc (rep ZZZ k) ZZZ [true],rep_snoc ZZZ k] using h

def ticks : Nat → Nat
  | 0 => 0
  | k+1 => ticks k + (14*k+16) + ticks k

theorem fill (k : Nat) (R : List Bool) :
    run0 table (ticks k) (sec (rep ZZZ k++R)) = some (sec (rep OZZ k++R)) := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    have h1 := ih (ZZZ++R)
    have h2 := increment k R
    have h3 := ih (OZZ++R)
    simp only [List.append_assoc] at h1 h2 h3
    have h := join0 (join0 h1 h2) h3
    simpa only [ticks,rep,List.append_assoc,← List.append_assoc (rep ZZZ k) ZZZ R,rep_snoc ZZZ k,
      ← List.append_assoc (rep OZZ k) OZZ R,rep_snoc OZZ k] using h

def family (n : Nat) := sec (rep ZZZ n++[true])
theorem entry : run0 table 16 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem growth (n : Nat) : run0 table (ticks n+14*n+30) (family n) = some (family (n+1)) := by
  rw [show ticks n+14*n+30=ticks n+(14*n+30) by omega]
  exact join0 (fill n [true]) (overflow n)
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 16 (fun n => ticks n+14*n+30) entry (by intro n; omega) growth m hm
#print axioms never
end BB6.Agent6Raw57RB1Pumps.M240
