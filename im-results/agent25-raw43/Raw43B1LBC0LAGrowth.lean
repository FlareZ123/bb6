import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43B1LBC0LAGrowth
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

def table (v : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,if v then 5 else 4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some (if v then ⟨true,false,0⟩ else ⟨false,false,5⟩))
  | 4,true => if v then none else some (some ⟨true,true,1⟩)
  | 5,false => some (some (if v then ⟨false,false,4⟩ else ⟨true,false,0⟩))
  | 5,true => if v then some (some ⟨true,true,1⟩) else none
  | _,_ => none

def T : List Bool := [true,false,false]
def Z : List Bool := [false,false,false]
def U : List Bool := [false,true,false]
def E : List Bool := [false,true]
def A (k : Nat) (R : List Bool) : Z0 := ⟨0,rep T k++[true,true],R⟩
def B (k : Nat) (R : List Bool) : Z0 := ⟨1,Z++(rep T k++[true,true]),R⟩
inductive Good : List Bool → Prop where
  | stop : Good E
  | t {R} : Good R → Good (T++R)
  | z {R} : Good R → Good (Z++R)
  | u {R} : Good R → Good (U++R)
inductive Inv : Z0 → Prop where
  | a (k R) : Good R → Inv (A k R)
  | b (k R) : Good R → Inv (B k R)
  | empty (k) : Inv (B k [])
private theorem aPop (v : Bool) (k : Nat) (R : List Bool) : run0 (table v) 3 (A (k+1) R) = some (A k (T++R)) := by cases v <;> rfl
private theorem aT (v : Bool) (R : List Bool) : run0 (table v) 4 (A 0 (T++R)) = some (A 0 (Z++R)) := by cases v <;> rfl
private theorem aZ (v : Bool) (R : List Bool) : run0 (table v) 10 (A 0 (Z++R)) = some (A 0 (U++R)) := by cases v <;> rfl
private theorem aU (v : Bool) (R : List Bool) : run0 (table v) 5 (A 0 (U++R)) = some (B 0 R) := by cases v <;> rfl
private theorem aE (v : Bool) : run0 (table v) 5 (A 0 E) = some (B 0 []) := by cases v <;> rfl
private theorem bT (v : Bool) (k : Nat) (R : List Bool) : run0 (table v) 2 (B k (T++R)) = some (A (k+1) (Z++R)) := by cases v <;> rfl
private theorem bZ (v : Bool) (k : Nat) (R : List Bool) : run0 (table v) 8 (B k (Z++R)) = some (A (k+1) (U++R)) := by cases v <;> rfl
private theorem bU (v : Bool) (k : Nat) (R : List Bool) : run0 (table v) 3 (B k (U++R)) = some (B (k+1) R) := by cases v <;> rfl
private theorem bE (v : Bool) (k : Nat) : run0 (table v) 3 (B k E) = some (B (k+1) []) := by cases v <;> rfl
private theorem bEmpty (v : Bool) (k : Nat) : run0 (table v) 8 (B k []) = some (A (k+1) E) := by cases v <;> rfl
private theorem advance (v : Bool) (z : Z0) (h : Inv z) : ∃ k z', 0<k ∧ run0 (table v) k z=some z' ∧ Inv z' := by
  cases h with
  | a k R g =>
    cases k with
    | succ k => exact ⟨3,_,by decide,aPop v k R,.a _ _ (.t g)⟩
    | zero => cases g with
      | stop => exact ⟨5,_,by decide,aE v,.empty _⟩
      | t g => exact ⟨4,_,by decide,aT v _,.a _ _ (.z g)⟩
      | z g => exact ⟨10,_,by decide,aZ v _,.a _ _ (.u g)⟩
      | u g => exact ⟨5,_,by decide,aU v _,.b _ _ g⟩
  | b k R g => cases g with
    | stop => exact ⟨3,_,by decide,bE v k,.empty _⟩
    | t g => exact ⟨2,_,by decide,bT v k _,.a _ _ (.z g)⟩
    | z g => exact ⟨8,_,by decide,bZ v k _,.a _ _ (.u g)⟩
    | u g => exact ⟨3,_,by decide,bU v k _,.b _ _ g⟩
  | empty k => exact ⟨8,_,by decide,bEmpty v k,.a _ _ .stop⟩
private theorem first (v : Bool) : run0 (table v) 9 ⟨0,[],[]⟩ = some (A 0 E) := by cases v <;> rfl
theorem live_prefix (v : Bool) (n : Nat) : ∃ t z, n≤t ∧ run0 (table v) t ⟨0,[],[]⟩=some z ∧ Inv z := by
  induction n with
  | zero => exact ⟨9,_,by decide,first v,.a _ _ .stop⟩
  | succ n ih =>
    obtain ⟨t,z,ht,hr,hi⟩ := ih
    obtain ⟨k,z',hk,h,hi'⟩ := advance v z hi
    exact ⟨t+k,z',by omega,join0 hr h,hi'⟩
theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  intro n
  obtain ⟨t,z,ht,hr,hi⟩ := live_prefix v n
  have hz : (zrun (table v) t start).map project = some z :=
    (run_project (table v) t start).trans hr
  cases hZ : zrun (table v) t start with
  | none => simp [hZ] at hz
  | some z' =>
    have H := zrun_sound (table v) m hm t start z' hZ
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl
#print axioms live_prefix
#print axioms never
end BB6.Agent25Raw43B1LBC0LAGrowth
