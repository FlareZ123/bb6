import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43B1LBC1LEM103
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | _,_ => none

def P : List Bool := [false,true,false]
def D0 : List Bool := [false,false,true]
def D1 : List Bool := [true,false,true]
def D2 : List Bool := [false,false,false]
def D3 : List Bool := [true,false,false]
def A (L : List Bool) (k : Nat) : Z0 := ⟨0,L,false::(rep P k++[true,true])⟩
def B (L : List Bool) (k : Nat) : Z0 := ⟨1,[false,false,false]++L,rep P k++[true,true]⟩
inductive Good : List Bool → Prop where
  | empty : Good []
  | one : Good [true]
  | d0 {L} : Good L → Good (D0++L)
  | d1 {L} : Good L → Good (D1++L)
  | d2 {L} : Good L → Good (D2++L)
  | d3 {L} : Good L → Good (D3++L)
inductive Inv : Z0 → Prop where
  | a L k : Good L → Inv (A L k)
  | b L k : Good ([false,false]++L) → Inv (B L k)
private theorem a0 (L : List Bool) : run0 table 6 (A (D0++L) 0) = some (A (D1++L) 0) := by rfl
private theorem a2 (L : List Bool) : run0 table 6 (A (D2++L) 0) = some (A (D3++L) 0) := by rfl
private theorem a1 (L : List Bool) (k : Nat) : run0 table 5 (A (D1++L) k) = some (B (false::L) k) := by rfl
private theorem a3 (L : List Bool) (k : Nat) : run0 table 3 (A (D3++L) k) = some (A L (k+1)) := by rfl
private theorem a0s (L : List Bool) (k : Nat) : run0 table 4 (A (D0++L) (k+1)) = some (B ([true,true,false,true]++L) k) := by rfl
private theorem a2s (L : List Bool) (k : Nat) : run0 table 4 (A (D2++L) (k+1)) = some (B ([true,true,false,false]++L) k) := by rfl
private theorem aEmpty : run0 table 6 (A [] 0) = some (A [true] 0) := by rfl
private theorem aEmptyS (k : Nat) : run0 table 4 (A [] (k+1)) = some (B [true,true] k) := by rfl
private theorem aOne (k : Nat) : run0 table 3 (A [true] k) = some (A [] (k+1)) := by rfl
private theorem b0 (L : List Bool) : run0 table 5 (B L 0) = some (A ([false,false]++L) 0) := by rfl
private theorem bs (L : List Bool) (k : Nat) : run0 table 3 (B L (k+1)) = some (B ([true,false,false]++L) k) := by rfl
private theorem advance (z : Z0) (h : Inv z) : ∃ k z', 0<k ∧ run0 table k z=some z' ∧ Inv z' := by
  cases h with
  | a L k g => cases g with
    | empty => cases k with
      | zero => exact ⟨6,_,by decide,aEmpty,.a _ _ .one⟩
      | succ k => exact ⟨4,_,by decide,aEmptyS k,.b _ _ (.d0 .one)⟩
    | one => exact ⟨3,_,by decide,aOne k,.a _ _ .empty⟩
    | d0 g => cases k with
      | zero => exact ⟨6,_,by decide,a0 _,.a _ _ (.d1 g)⟩
      | succ k => exact ⟨4,_,by decide,a0s _ k,.b _ _ (.d0 (.d1 g))⟩
    | d1 g => exact ⟨5,_,by decide,a1 _ k,.b _ _ (.d2 g)⟩
    | d2 g => cases k with
      | zero => exact ⟨6,_,by decide,a2 _,.a _ _ (.d3 g)⟩
      | succ k => exact ⟨4,_,by decide,a2s _ k,.b _ _ (.d0 (.d3 g))⟩
    | d3 g => exact ⟨3,_,by decide,a3 _ k,.a _ _ g⟩
  | b L k g => cases k with
    | zero => exact ⟨5,_,by decide,b0 L,.a _ _ g⟩
    | succ k => exact ⟨3,_,by decide,bs L k,.b _ _ (.d0 g)⟩
private theorem first : run0 table 12 ⟨0,[],[]⟩ = some (A [true] 0) := by rfl
theorem live_prefix (n : Nat) : ∃ t z, n≤t ∧ run0 table t ⟨0,[],[]⟩=some z ∧ Inv z := by
  induction n with
  | zero => exact ⟨12,_,by decide,first,.a _ _ .one⟩
  | succ n ih =>
    obtain ⟨t,z,ht,hr,hi⟩ := ih
    obtain ⟨k,z',hk,h,hi'⟩ := advance z hi
    exact ⟨t+k,z',by omega,join0 hr h,hi'⟩
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨t,z,ht,hr,hi⟩ := live_prefix n
  have hz : (zrun table t start).map project = some z :=
    (run_project table t start).trans hr
  cases hZ : zrun table t start with
  | none => simp [hZ] at hz
  | some z' =>
    have H := zrun_sound table m hm t start z' hZ
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl
#print axioms live_prefix
#print axioms never
end BB6.Agent25Raw43B1LBC1LEM103
