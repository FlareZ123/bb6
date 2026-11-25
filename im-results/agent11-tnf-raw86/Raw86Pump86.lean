import SweepPumping
set_option maxRecDepth 100000
namespace BB6.Agent11Raw86Pump86
open BB6Coverage BB6Coverage.Agent31Pump

def table (b : Bool) : PartialMachine := fun (q,s) =>
  match q.val,s with
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
  | 5,false => some (some ⟨b,b,1⟩)
  | 5,true  => some (some ⟨false,false,1⟩)
  | _,_ => none
abbrev B (l r : List Bool) : Z0 := ⟨1,l,r⟩
abbrev C (l r : List Bool) : Z0 := ⟨2,l,r⟩
abbrev X : List Bool := [false,true,false,true]
abbrev Y : List Bool := [true,true,false,true]
abbrev P : List Bool := [false,true]
abbrev T : List Bool := [true,false,true]
def family (n : Nat) : Z0 := B [] (rep X (n+1))
def lc (b : Bool) : Nat := if b then 6 else 4
def fc (b : Bool) : Nat := if b then 8 else 4
theorem first (b : Bool) : run0 (table b) 9 ⟨0,[],[]⟩ = some (family 0) := by cases b <;> decide
theorem enter (b : Bool) (R : List Bool) : run0 (table b) 1 (B [] ([false]++R)) = some (C P R) := by cases b <;> rfl
theorem right_one (b : Bool) (L R : List Bool) :
    run0 (table b) 6 (C (P++L) ([true]++X++R)) = some (C (P++Y++L) ([true]++R)) := by cases b <;> rfl
theorem turn (b : Bool) (L : List Bool) :
    run0 (table b) 6 (C (P++L) T) = some (C ([false,true,true,true,false,true]++L) []) := by cases b <;> rfl
theorem turn2 (b : Bool) (L : List Bool) :
    run0 (table b) 7 (C ([false,true,true,true,false,true]++L) []) = some (B (T++L) X) := by cases b <;> rfl
theorem left_one (b : Bool) (L R : List Bool) :
    run0 (table b) (lc b) (B (T++Y++L) R) = some (B (T++L) (X++R)) := by cases b <;> rfl
theorem finish (b : Bool) (R : List Bool) :
    run0 (table b) (fc b) (B T R) = some (B [] (X++R)) := by cases b <;> rfl
theorem rotate (n : Nat) : [false,true] ++ rep X n ++ P = rep X (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change [false,true] ++ (X ++ rep X n) ++ P = X ++ rep X (n+1)
    rw [← ih]
    rfl
theorem growth (b : Bool) (n : Nat) : run0 (table b) ((6+lc b)*n+14+fc b) (family n) = some (family (n+1)) := by
  have h0 := enter b ([true]++rep X n++P)
  have h1 := sweepR (table b) 2 P [true] X Y 6 (right_one b) n [] P
  have h2 := turn b (rep Y n)
  have h3 := turn2 b (rep Y n)
  have h4 := sweepL (table b) 1 T [] Y X (lc b) (left_one b) n [] X
  have h5 := finish b (rep X n++X)
  simp only [List.nil_append,List.append_nil] at h1 h4
  have hh0 : run0 (table b) 1 (family n) = some (C P ([true]++rep X n++P)) := by
    rw [family, ← rotate n]; exact h0
  have H := join0 (join0 (join0 (join0 (join0 hh0 h1) h2) h3) h4) h5
  have hs : X++(rep X n++X) = rep X (n+1+1) := by rw [rep_snoc X n]; rfl
  rw [hs] at H
  have hc : (6+lc b)*n+14+fc b = 1+6*n+6+7+lc b*n+fc b := by cases b <;> simp [lc,fc] <;> omega
  rw [hc]
  exact H
theorem never (b : Bool) (m : Machine) (hm : compatible (table b) m) : NeverHalts m :=
  never_of_growth (table b) family 9 (fun n => (6+lc b)*n+14+fc b)
    (first b) (by intro n; cases b <;> simp [lc,fc] <;> omega) (growth b) m hm
#print axioms first
#print axioms growth
#print axioms never
end BB6.Agent11Raw86Pump86
