import SweepPumping
set_option maxRecDepth 100000
namespace BB6.Agent11Raw86PumpTail
open BB6Coverage BB6Coverage.Agent31Pump

/-- A1 = 0LC, 0LD, 0RC, 0RD; independently F0 = 1RE or 1RF. -/
def table (r d b : Bool) : PartialMachine := fun (q,s) =>
  match q.val,s with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some ⟨false,r,if d then 3 else 2⟩)
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
abbrev I : List Bool := [false,false,true]
abbrev Y : List Bool := [true,false,true]
abbrev P : List Bool := [false,true]
def sect (n : Nat) (S : List Bool) : Z0 := B [] ([false]++rep X n++S)

theorem enter (r d b : Bool) (R : List Bool) : run0 (table r d b) 1 (B [] ([false]++R)) = some (C P R) := by cases r <;> cases d <;> cases b <;> rfl
theorem right_one (r d b : Bool) (L R : List Bool) :
    run0 (table r d b) 7 (C (P++L) ([true]++I++R)) = some (C (P++Y++L) ([true]++R)) := by cases r <;> cases d <;> cases b <;> rfl
theorem left_one (r d b : Bool) (L R : List Bool) :
    run0 (table r d b) 5 (B (Y++L) ([false]++R)) = some (B L ([false]++X++R)) := by cases r <;> cases d <;> cases b <;> rfl
theorem rotate (n : Nat) (S : List Bool) : [true] ++ rep I n ++ S = rep X n ++ ([true]++S) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change [true] ++ (I ++ rep I n) ++ S = (X ++ rep X n) ++ ([true]++S)
    simp only [I,X,List.cons_append,List.nil_append]
    have h := ih
    simp only [I,X,List.singleton_append] at h
    rw [← h]
    rfl

theorem rep_add (W : List Bool) (k n : Nat) : rep W k ++ rep W n = rep W (k+n) := by
  induction k with
  | zero => simp [rep]
  | succ k ih => rw [show k+1+n=(k+n)+1 by omega]; simp only [rep,List.append_assoc,ih]

/-- The middle control is a constant-size suffix rewrite. Two unbounded sweeps
    are factored out once for all eight tables. -/
theorem transfer (r d b : Bool) (n k c : Nat) (S R : List Bool)
    (h : ∀ L, run0 (table r d b) c (C (P++L) ([true]++S)) = some (B (rep Y k++L) ([false]++R))) :
    run0 (table r d b) (1+7*n+c+5*(k+n)) (sect n ([true]++S)) = some (sect (k+n) R) := by
  have h0 := enter r d b (rep X n++([true]++S))
  have h1 := sweepR (table r d b) 2 P [true] I Y 7 (right_one r d b) n [] S
  have h2 := h (rep Y n)
  have h3 := sweepL (table r d b) 1 [] [false] Y X 5 (left_one r d b) (k+n) [] R
  simp only [List.nil_append,List.append_nil] at h1 h3
  rw [rotate n S] at h1
  rw [rep_add Y k n] at h2
  exact join0 (join0 (join0 h0 h1) h2) h3

abbrev ff := table false false
abbrev ft := table false true
abbrev tf := table true false
abbrev tt := table true true

theorem turn51 (b : Bool) (L : List Bool) :
    run0 (ff b) 22 (C (P++L) [true]) = some (B (rep Y 2++L) [false,true]) := by cases b <;> rfl
theorem turn53 (b : Bool) (L : List Bool) :
    run0 (ft b) 20 (C (P++L) [true,false,false,false]) = some (B (rep Y 2++L) [false,false]) := by cases b <;> rfl
theorem turn56a (b : Bool) (L : List Bool) :
    run0 (tf b) 3 (C (P++L) [true,true,true]) = some (B (rep Y 1++L) [false,true]) := by cases b <;> rfl
theorem turn56b (b : Bool) (L : List Bool) :
    run0 (tf b) 24 (C (P++L) [true]) = some (B (rep Y 2++L) [false,true,true,true]) := by cases b <;> rfl
theorem turn58a (b : Bool) (L : List Bool) :
    run0 (tt b) 3 (C (P++L) [true,true]) = some (B (rep Y 1++L) [false]) := by cases b <;> rfl
theorem turn58b (b : Bool) (L : List Bool) :
    run0 (tt b) 22 (C (P++L) [true,false,false]) = some (B (rep Y 2++L) [false,true,true]) := by cases b <;> rfl

def family51 (n : Nat) := sect (2*n+1) [true]
def family53 (n : Nat) := sect n [true,false,false,false]
def family56 (n : Nat) := sect (3*n+1) [true,true,true]
def family58 (n : Nat) := sect (2*n+1) [true,true]
theorem first51 (b : Bool) : run0 (ff b) 24 ⟨0,[],[]⟩ = some (family51 0) := by cases b <;> decide
theorem first53 (b : Bool) : run0 (ft b) 22 ⟨0,[],[]⟩ = some (family53 0) := by cases b <;> decide
theorem first56 (b : Bool) : run0 (tf b) 26 ⟨0,[],[]⟩ = some (family56 0) := by cases b <;> decide
theorem first58 (b : Bool) : run0 (tt b) 24 ⟨0,[],[]⟩ = some (family58 0) := by cases b <;> decide

theorem growth51 (b : Bool) (n : Nat) : run0 (ff b) (24*n+45) (family51 n) = some (family51 (n+1)) := by
  have h := transfer false false b (2*n+1) 2 22 [] [true] (turn51 b)
  rw [show 1+7*(2*n+1)+22+5*(2+(2*n+1))=24*n+45 by omega] at h
  rw [show 2+(2*n+1)=2*(n+1)+1 by omega] at h
  exact h

theorem growth53 (b : Bool) (n : Nat) : run0 (ft b) (12*n+31) (family53 n) = some (family53 (n+1)) := by
  have h := transfer false true b n 2 20 [false,false,false] [false] (turn53 b)
  have hs : sect (2+n) [false] = sect (n+1) [true,false,false,false] := by
    rw [show 2+n=(n+1)+1 by omega]
    unfold sect
    rw [show rep X (n+1+1) = rep X (n+1) ++ X by rw [rep_snoc]; rfl]
    simp only [List.append_assoc]; rfl
  rw [hs] at h
  rw [show 1+7*n+20+5*(2+n)=12*n+31 by omega] at h
  exact h

theorem growth56 (b : Bool) (n : Nat) : run0 (tf b) (72*n+80) (family56 n) = some (family56 (n+1)) := by
  have h1 := transfer true false b (3*n+1) 1 3 [true,true] [true] (turn56a b)
  have h2 := transfer true false b (1+(3*n+1)) 2 24 [] [true,true,true] (turn56b b)
  have H := join0 h1 h2
  rw [show 1+7*(3*n+1)+3+5*(1+(3*n+1))+(1+7*(1+(3*n+1))+24+5*(2+(1+(3*n+1))))=72*n+80 by omega] at H
  rw [show 2+(1+(3*n+1))=3*(n+1)+1 by omega] at H
  exact H

theorem growth58 (b : Bool) (n : Nat) : run0 (tt b) (48*n+66) (family58 n) = some (family58 (n+1)) := by
  have h1 := transfer true true b (2*n+1) 1 3 [true] [] (turn58a b)
  have hs : sect (1+(2*n+1)) [] = sect (2*n+1) X := by
    rw [Nat.add_comm 1 (2*n+1)]
    unfold sect
    rw [show rep X (2*n+1+1) = rep X (2*n+1) ++ X by rw [rep_snoc]; rfl]
    simp only [List.append_assoc,List.append_nil]
  rw [hs] at h1
  have h2 := transfer true true b (2*n+1) 2 22 [false,false] [true,true] (turn58b b)
  have H := join0 h1 h2
  rw [show 1+7*(2*n+1)+3+5*(1+(2*n+1))+(1+7*(2*n+1)+22+5*(2+(2*n+1)))=48*n+66 by omega] at H
  rw [show 2+(2*n+1)=2*(n+1)+1 by omega] at H
  exact H
theorem never51 (b : Bool) (m : Machine) (hm : compatible (ff b) m) : NeverHalts m :=
  never_of_growth (ff b) family51 24 (fun n => 24*n+45) (first51 b) (by intro n; omega) (growth51 b) m hm
theorem never53 (b : Bool) (m : Machine) (hm : compatible (ft b) m) : NeverHalts m :=
  never_of_growth (ft b) family53 22 (fun n => 12*n+31) (first53 b) (by intro n; omega) (growth53 b) m hm
theorem never56 (b : Bool) (m : Machine) (hm : compatible (tf b) m) : NeverHalts m :=
  never_of_growth (tf b) family56 26 (fun n => 72*n+80) (first56 b) (by intro n; omega) (growth56 b) m hm
theorem never58 (b : Bool) (m : Machine) (hm : compatible (tt b) m) : NeverHalts m :=
  never_of_growth (tt b) family58 24 (fun n => 48*n+66) (first58 b) (by intro n; omega) (growth58 b) m hm
#print axioms growth51
#print axioms growth53
#print axioms growth56
#print axioms growth58
#print axioms never51
#print axioms never53
#print axioms never56
#print axioms never58
end BB6.Agent11Raw86PumpTail
