import SweepPumping
set_option maxRecDepth 100000
namespace BB6.Agent10Raw87Pump
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun (q,b) =>
  match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => none
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true  => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 4,true  => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true  => some (some ⟨false,true,1⟩)
  | _,_ => none

def rep (b : List Bool) : Nat → List Bool
  | 0 => []
  | n+1 => b ++ rep b n
abbrev X := [true,false,true,false]
abbrev Y := [true,true,false,true]
abbrev Z := [true,false,true]
abbrev C (l r : List Bool) : Z0 := ⟨2,l,r⟩
abbrev F (l r : List Bool) : Z0 := ⟨5,l,r⟩

def family (n : Nat) : Z0 := F [] (rep X (n+1) ++ Z)
theorem first : run0 table 30 ⟨0,[],[]⟩ = some (family 0) := by decide

theorem enter (R : List Bool) :
    run0 table 2 (F [] (true::R)) = some (C [false,true] (true::R)) := by rfl

theorem right_one (L R : List Bool) :
    run0 table 6 (C ([false,true]++L) (X++R)) = some (C ([false,true]++Y++L) R) := by rfl

theorem right_many (n k : Nat) :
    run0 table (6*n) (C ([false,true]++rep Y k) (rep X n ++ Z)) =
      some (C ([false,true]++rep Y (n+k)) Z) := by
  induction n generalizing k with
  | zero => simp [run0,rep]
  | succ n ih =>
    have h := right_one (rep Y k) (rep X n ++ Z)
    have h' := ih (k+1)
    have H := join0 h h'
    rw [show 6*(n+1)=6+6*n by omega, show n+1+k=n+(k+1) by omega]
    simpa only [rep,List.append_assoc] using H

theorem turn (L : List Bool) :
    run0 table 12 (C ([false,true]++L) Z) = some (F (Y++L) Z) := by rfl

theorem left_one (L : List Bool) (k : Nat) :
    run0 table 6 (F (Y++L) (rep X k ++ Z)) = some (F L (X++(rep X k ++ Z))) := by
  cases k <;> rfl

theorem left_many (n k : Nat) :
    run0 table (6*n) (F (rep Y n) (rep X k ++ Z)) =
      some (F [] (rep X (n+k) ++ Z)) := by
  induction n generalizing k with
  | zero => simp [run0,rep]
  | succ n ih =>
    have h := left_one (rep Y n) k
    have h' := ih (k+1)
    have H := join0 h h'
    rw [show 6*(n+1)=6+6*n by omega, show n+1+k=n+(k+1) by omega]
    simpa only [rep,List.append_assoc] using H

theorem growth (n : Nat) :
    run0 table (12*n+32) (family n) = some (family (n+1)) := by
  have h0 : run0 table 2 (family n) = some (C ([false,true]++rep Y 0) (rep X (n+1)++Z)) := by
    unfold family
    simp only [rep, List.append_nil]
    exact enter _
  have h1 := right_many (n+1) 0
  simp only [Nat.add_zero] at h1
  have h2 := turn (rep Y (n+1))
  have h3 := left_many (n+2) 0
  simp only [rep,List.nil_append] at h3
  have H := join0 (join0 (join0 h0 h1) h2) h3
  rw [show 12*n+32=2+6*(n+1)+12+6*(n+2) by omega]
  exact H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 30 (fun n => 12*n+32) first (by intro n; omega) growth m hm

#print axioms first
#print axioms growth
#print axioms never
end BB6.Agent10Raw87Pump
