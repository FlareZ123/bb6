import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw98
open BB6Coverage BB6Coverage.Agent31Pump

namespace Unary

def table : PartialMachine := fun (q,b) =>
  match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true  => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true  => some (some ⟨false,false,1⟩)
  | 5,false => none
  | 5,true  => some (some ⟨false,false,4⟩)
  | _,_ => none

abbrev O := [false]
abbrev I := [true]
abbrev C (l r : List Bool) : Z0 := ⟨2,l,r⟩
abbrev D (l r : List Bool) : Z0 := ⟨3,l,r⟩

def family (n : Nat) : Z0 := D (rep O (n+3) ++ [true,true,false] ++ rep I (n+2)) []
theorem first : run0 table 21 ⟨0,[],[]⟩ = some (family 0) := by decide

private theorem dOne (L R : List Bool) : run0 table 1 (D (O++L) R) = some (D L (I++R)) := by rfl
private theorem cOne (L R : List Bool) : run0 table 1 (C (I++L) (I++R)) = some (C (I++O++L) R) := by rfl
private theorem turn (L R : List Bool) :
    run0 table 16 (D ([true,true,false,true,true]++L) ([true,true,true]++R)) =
      some (C ([true,true,true,false,true,true,true]++L) ([true]++R)) := by rfl

private theorem dMany (n : Nat) : run0 table (n+3) (family n) =
    some (D ([true,true,false]++rep I (n+2)) (rep I (n+3))) := by
  simpa [family] using sweepL table 3 [] [] O I 1 dOne (n+3) ([true,true,false]++rep I (n+2)) []

private theorem cMany (n : Nat) (L : List Bool) :
    run0 table (n+1) (C (I++L) (rep I (n+1))) = some (C (I++rep O (n+1)++L) []) := by
  simpa using sweepR table 2 I [] I O 1 cOne (n+1) L []

private theorem finish (L : List Bool) :
    run0 table 2 (C (I++L) []) = some (D ([false,false,false]++L) []) := by rfl

theorem growth (n : Nat) : run0 table (2*n+22) (family n) = some (family (n+1)) := by
  have h1 := dMany n
  have h2 := turn (rep I n) (rep I n)
  have h2' : run0 table 16 (D ([true,true,false]++rep I (n+2)) (rep I (n+3))) =
    some (C (I++[true,true,false]++rep I (n+3)) (rep I (n+1))) := by
    simpa [rep,List.append_assoc] using h2
  have h3 := cMany n ([true,true,false]++rep I (n+3))
  have h4 := finish (rep O (n+1)++[true,true,false]++rep I (n+3))
  have H := join0 (join0 (join0 h1 h2') h3) (by simpa only [List.append_assoc] using h4)
  rw [show 2*n+22=(n+3)+16+(n+1)+2 by omega]
  simpa [family,rep,List.append_assoc,Nat.add_assoc] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 21 (fun n => 2*n+22) first (by intro n; omega) growth m hm
#print axioms never
end Unary

namespace Alternate

def table (v : Bool) : PartialMachine := fun (q,b) =>
  match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some ⟨false,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => none
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true  => some (some ⟨true,true,4⟩)
  | 4,false => if v then some (some ⟨true,true,3⟩) else some (some ⟨true,false,5⟩)
  | 4,true  => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true  => some (some ⟨false,false,4⟩)
  | _,_ => none

abbrev X := [true,false]
abbrev Y := [false,true]
abbrev F (l r : List Bool) : Z0 := ⟨5,l,r⟩
def costL (v : Bool) : Nat := if v then 6 else 2

theorem right_one (v : Bool) (L R : List Bool) :
    run0 (table v) 2 (F ([false]++L) (X++R)) = some (F ([false]++Y++L) R) := by rfl

theorem right_start (v : Bool) (R : List Bool) :
    run0 (table v) 2 (F [] (X++R)) = some (F ([false]++Y) R) := by rfl

theorem right_many (v : Bool) (n : Nat) (R : List Bool) :
    run0 (table v) (2*(n+1)) (F [] (rep X (n+1)++R)) = some (F ([false]++rep Y (n+1)) R) := by
  have h1 := right_start v (rep X n++R)
  have h2 := sweepR (table v) 5 [false] [] X Y 2 (right_one v) n Y R
  have H := join0 h1 (by simpa using h2)
  rw [show 2*(n+1)=2+2*n by omega]
  simpa [rep,List.append_assoc,← rep_snoc Y n] using H

theorem left_one (v : Bool) (L R : List Bool) :
    run0 (table v) (costL v) (F (X++L) R) = some (F L (X++R)) := by cases v <;> rfl

theorem left_end (v : Bool) (R : List Bool) :
    run0 (table v) (costL v) (F [true] R) = some (F [] (X++R)) := by cases v <;> rfl

theorem left_many (v : Bool) (n : Nat) (R : List Bool) :
    run0 (table v) (costL v*(n+1)) (F (rep X n++[true]) R) = some (F [] (rep X (n+1)++R)) := by
  have h1 := sweepL (table v) 5 [] [] X X (costL v) (left_one v) n [true] R
  have h2 := left_end v (rep X n++R)
  rw [Nat.mul_succ]
  simpa [rep,List.append_assoc] using join0 (by simpa using h1) h2

private theorem rotateXY (n : Nat) : [true]++rep Y n = rep X n++[true] := by
  exact rotate true [false] n

private theorem turn1 (v : Bool) (L : List Bool) :
    run0 (table v) 2 (F ([false]++L) [true,true,false,true]) = some (F ([true,false,true]++L) [false,true]) := by rfl
private theorem turn2 (v : Bool) (L : List Bool) :
    run0 (table v) 12 (F ([false,false,true]++L) [false,true]) = some (F ([true]++L) [true,false,true,true]) := by rfl
private theorem turn3 (v : Bool) (L : List Bool) :
    run0 (table v) 2 (F ([false]++L) [true,true]) = some (F ([true,false,true]++L) []) := by rfl
private theorem turn4 (v : Bool) (L : List Bool) :
    run0 (table v) 18 (F ([false,false,true]++L) []) = some (F ([true]++L) [true,false,true,true,false,true]) := by rfl

def phase1 (n : Nat) := F [] (rep X (n+1)++[true,true,false,true])
def phase2 (n : Nat) := F [] (rep X (n+3)++[false,true])
def phase3 (n : Nat) := F [] (rep X (n+4)++[true,true])
def phase4 (n : Nat) := F [] (rep X (n+6))

theorem p12 (v : Bool) (n : Nat) :
    run0 (table v) (2*(n+1)+2+costL v*(n+3)) (phase1 n) = some (phase2 n) := by
  have h1 := right_many v n [true,true,false,true]
  have h2 := turn1 v (rep Y (n+1))
  have h2' : run0 (table v) 2 (F ([false]++rep Y (n+1)) [true,true,false,true]) =
    some (F (rep X (n+2)++[true]) [false,true]) := by
    rw [show [true,false,true]++rep Y (n+1)=X++([true]++rep Y (n+1)) by rfl,rotateXY] at h2
    exact h2
  have h3 := left_many v (n+2) [false,true]
  exact join0 (join0 h1 h2') h3

theorem p23 (v : Bool) (n : Nat) :
    run0 (table v) (2*(n+3)+12+costL v*(n+3)) (phase2 n) = some (phase3 n) := by
  have h1 := right_many v (n+2) [false,true]
  have h2 := turn2 v (rep Y (n+2))
  rw [rotateXY] at h2
  have h2' : run0 (table v) 12 (F ([false]++rep Y (n+3)) [false,true]) =
    some (F (rep X (n+2)++[true]) (X++[true,true])) := by
    exact h2
  have h3 := left_many v (n+2) (X++[true,true])
  have H := join0 (join0 h1 h2') h3
  unfold phase2 phase3
  simpa only [rep_snoc,List.append_assoc,← rep_snoc X (n+3),← List.append_assoc (rep X (n+3)) X [true,true],show rep X (n+3)++X=rep X (n+4) by rw [rep_snoc]; rfl] using H

theorem p34 (v : Bool) (n : Nat) :
    run0 (table v) (2*(n+4)+2+costL v*(n+6)) (phase3 n) = some (phase4 n) := by
  have h1 := right_many v (n+3) [true,true]
  have h2 := turn3 v (rep Y (n+4))
  have h2' : run0 (table v) 2 (F ([false]++rep Y (n+4)) [true,true]) =
    some (F (rep X (n+5)++[true]) []) := by
    rw [show [true,false,true]++rep Y (n+4)=X++([true]++rep Y (n+4)) by rfl,rotateXY] at h2
    exact h2
  have h3 := left_many v (n+5) []
  simpa [phase3,phase4] using join0 (join0 h1 h2') h3

theorem p41 (v : Bool) (n : Nat) :
    run0 (table v) (2*(n+6)+18+costL v*(n+6)) (phase4 n) = some (phase1 (n+6)) := by
  have h1 := right_many v (n+5) []
  have h2 := turn4 v (rep Y (n+5))
  rw [rotateXY] at h2
  have h2' : run0 (table v) 18 (F ([false]++rep Y (n+6)) []) =
    some (F (rep X (n+5)++[true]) (X++[true,true,false,true])) := by
    exact h2
  have h3 := left_many v (n+5) (X++[true,true,false,true])
  have H := join0 (join0 h1 h2') h3
  unfold phase1 phase4
  have he : rep X (n+6) ++ (X++[true,true,false,true])=rep X (n+7)++[true,true,false,true] := by
    rw [←List.append_assoc,rep_snoc]; rfl
  simpa only [List.append_nil,he] using H

def family (n : Nat) := phase1 (6*n+3)
def entry (v : Bool) := if v then 56 else 40
def cost (v : Bool) (n : Nat) :=
    let a := 6*n+3
    (2*(a+1)+2+costL v*(a+3)) + (2*(a+3)+12+costL v*(a+3)) +
    (2*(a+4)+2+costL v*(a+6)) + (2*(a+6)+18+costL v*(a+6))
theorem first (v : Bool) : run0 (table v) (entry v) ⟨0,[],[]⟩ = some (family 0) := by cases v <;> decide
theorem growth (v : Bool) (n : Nat) : run0 (table v) (cost v n) (family n) = some (family (n+1)) := by
  have H := join0 (join0 (join0 (p12 v (6*n+3)) (p23 v (6*n+3))) (p34 v (6*n+3))) (p41 v (6*n+3))
  unfold family cost
  rw [show 6*(n+1)+3=6*n+3+6 by omega]
  exact H
theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) family (entry v) (cost v) (first v) (by intro n; cases v <;> simp [cost,costL] <;> omega) (growth v) m hm
#print axioms never
end Alternate
end BB6.Agent19Raw98
