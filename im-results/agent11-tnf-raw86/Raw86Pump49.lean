import SweepPumping
set_option maxRecDepth 100000
namespace BB6.Agent11Raw86Pump49
open BB6Coverage BB6Coverage.Agent31Pump

def table (b : Bool) : PartialMachine := fun (q,s) =>
  match q.val,s with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => none
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true  => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,0⟩)
  | 4,true  => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,true,if b then 5 else 4⟩)
  | 5,true  => some (some ⟨false,false,1⟩)
  | _,_ => none
abbrev B (l r : List Bool) : Z0 := ⟨1,l,r⟩
abbrev C (l r : List Bool) : Z0 := ⟨2,l,r⟩
abbrev X : List Bool := [true,false,false]
abbrev Y : List Bool := [true,false,true]
abbrev I : List Bool := [false,false,true]
abbrev T : List Bool := [false,true]
abbrev P : List Bool := [false,true]
def family (n : Nat) : Z0 := B [] ([false]++rep X n++Y)
theorem first (b : Bool) : run0 (table b) 9 ⟨0,[],[]⟩ = some (family 0) := by cases b <;> decide
theorem enter (b : Bool) (R : List Bool) : run0 (table b) 1 (B [] ([false]++R)) = some (C P R) := by cases b <;> rfl
theorem right_one (b : Bool) (L R : List Bool) :
    run0 (table b) 7 (C (P++L) ([true]++I++R)) = some (C (P++Y++L) ([true]++R)) := by cases b <;> rfl
theorem turn (b : Bool) (L : List Bool) :
    run0 (table b) 6 (C (P++L) Y) = some (C ([false,true,true,true,false,true]++L) []) := by cases b <;> rfl
theorem turn2 (b : Bool) (L : List Bool) :
    run0 (table b) 7 (C ([false,true,true,true,false,true]++L) []) = some (B (Y++L) ([false]++Y)) := by cases b <;> rfl
theorem left_one (b : Bool) (L R : List Bool) :
    run0 (table b) 5 (B (Y++L) ([false]++R)) = some (B L ([false]++X++R)) := by cases b <;> rfl
theorem rotate (n : Nat) : [true] ++ rep I n ++ T = rep X n ++ Y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change [true] ++ (I ++ rep I n) ++ T = (X ++ rep X n) ++ Y
    simp only [I,X,List.cons_append,List.nil_append]
    have h := ih
    simp only [List.singleton_append] at h
    rw [← h]
    rfl
theorem growth (b : Bool) (n : Nat) : run0 (table b) (12*n+19) (family n) = some (family (n+1)) := by
  have h0 := enter b (rep X n++Y)
  have h1 := sweepR (table b) 2 P [true] I Y 7 (right_one b) n [] T
  have h2 := turn b (rep Y n)
  have h3 := turn2 b (rep Y n)
  have h4 := sweepL (table b) 1 [] [false] Y X 5 (left_one b) (n+1) [] Y
  simp only [List.nil_append,List.append_nil] at h1 h4
  rw [rotate n] at h1
  change run0 (table b) (7*n) (C P (rep X n ++ Y)) = some (C (P++rep Y n) Y) at h1
  rw [show Y++rep Y n=rep Y (n+1) by rfl] at h3
  have H := join0 (join0 (join0 (join0 h0 h1) h2) h3) h4
  rw [show 12*n+19=1+7*n+6+7+5*(n+1) by omega]
  exact H
theorem never (b : Bool) (m : Machine) (hm : compatible (table b) m) : NeverHalts m :=
  never_of_growth (table b) family 9 (fun n => 12*n+19)
    (first b) (by intro n; omega) (growth b) m hm
#print axioms first
#print axioms growth
#print axioms never
end BB6.Agent11Raw86Pump49
