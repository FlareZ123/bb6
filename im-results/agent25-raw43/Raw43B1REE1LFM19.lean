import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43B1REE1LFM19
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def bits (s : String) : List Bool := s.toList.map (· == '1')
def blocks (B : List Bool) : Nat → List Bool
  | 0 => []
  | n+1 => B ++ blocks B n

def S := bits "00000100010"
def R := bits "00100010000"
def B := bits "11101111110"
def tail := bits "0000000100"
def A (n : Nat) : Z0 := ⟨0,bits "010",blocks S n++tail⟩
def mid (k n : Nat) : Z0 := ⟨0,bits "0101001111110"++blocks B k,bits "0000100"++blocks R n++bits "0000100"⟩
def F (k n : Nat) : Z0 := ⟨5,false::blocks B k,false::(blocks S n++tail)⟩

theorem rotate (n : Nat) : blocks S n++tail = bits "000"++blocks R n++bits "0000100" := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [blocks,List.append_assoc,ih]
    rfl

theorem prepare (W : List Bool) : run0 table 93 ⟨0,bits "010",S++bits "000"++W⟩ = some ⟨0,bits "0101001111110",bits "0000100"++W⟩ := by rfl

theorem enter (n : Nat) : run0 table 93 (A (n+1)) = some (mid 0 n) := by
  unfold A mid
  simp only [blocks,List.append_nil,List.append_assoc]
  rw [rotate n]
  simpa only [List.append_assoc] using prepare (blocks R n++bits "0000100")

theorem forward0 (L W : List Bool) : run0 table 111 ⟨0,bits "0101001111110"++L,bits "0000100"++R++W⟩ = some ⟨0,bits "0101001111110"++B++L,bits "0000100"++W⟩ := by rfl

theorem forward (k n : Nat) : run0 table 111 (mid k (n+1)) = some (mid (k+1) n) := by
  simpa only [mid,blocks,List.append_assoc] using forward0 (blocks B k) (blocks R n++bits "0000100")

theorem turn0 (L : List Bool) : run0 table 178 ⟨0,bits "0101001111110"++L,bits "00001000000100"⟩ = some ⟨0,bits "011111110"++B++B++L,[false]⟩ := by rfl

theorem startSweep (L : List Bool) : run0 table 18 ⟨0,bits "011111110"++L,[false]⟩ = some ⟨5,false::L,false::tail⟩ := by rfl

theorem turn (k : Nat) : run0 table 196 (mid k 0) = some (F (k+2) 0) := by
  have H := join0 (turn0 (blocks B k)) (startSweep (B++B++blocks B k))
  exact H

theorem back0 (L W : List Bool) : run0 table 11 ⟨5,false::(B++L),false::W⟩ = some ⟨5,false::L,false::(S++W)⟩ := by rfl

theorem back (k n : Nat) : run0 table 11 (F (k+1) n) = some (F k (n+1)) := by
  simpa only [F,blocks,List.append_assoc] using back0 (blocks B k) (blocks S n++tail)

theorem finish (W : List Bool) : run0 table 3 ⟨5,[false],false::W⟩ = some ⟨0,bits "010",W⟩ := by rfl

theorem finishF (n : Nat) : run0 table 3 (F 0 n) = some (A n) := by
  simpa only [F,A,blocks,List.nil_append] using finish (blocks S n++tail)

inductive Inv : Z0 → Prop
  | a (n : Nat) : Inv (A (n+1))
  | mid (k n : Nat) : Inv (mid k n)
  | back (k n : Nat) : 0<k+n → Inv (F k n)

theorem stepInv (z : Z0) (h : Inv z) : ∃ t z', 0<t ∧ run0 table t z=some z' ∧ Inv z' := by
  cases h with
  | a n => exact ⟨93,_,by omega,enter n,Inv.mid 0 n⟩
  | mid k n => cases n with
    | zero => exact ⟨196,_,by omega,turn k,Inv.back (k+2) 0 (by omega)⟩
    | succ n => exact ⟨111,_,by omega,forward k n,Inv.mid (k+1) n⟩
  | back k n h => cases k with
    | zero => cases n with
      | zero => omega
      | succ n => exact ⟨3,_,by omega,finishF (n+1),Inv.a n⟩
    | succ k => exact ⟨11,_,by omega,back k n,Inv.back k (n+1) (by omega)⟩

theorem start : run0 table 250 ⟨0,[],[]⟩ = some (A 1) := by rfl

theorem live (N : Nat) : ∃ t z, N≤t ∧ run0 table t ⟨0,[],[]⟩ = some z ∧ Inv z := by
  induction N with
  | zero => exact ⟨250,_,by omega,start,Inv.a 0⟩
  | succ N ih =>
    obtain ⟨t,z,ht,hz,hi⟩ := ih
    obtain ⟨a,z',ha,hr,hi'⟩ := stepInv z hi
    exact ⟨t+a,z',by omega,join0 hz hr,hi'⟩

open BB6Coverage.Agent50Zipper

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨t,z,ht,hr,_⟩ := live n
  let start : Z := ⟨0,0,[],[]⟩
  have hz : (zrun table t start).map project = some z :=
    (run_project table t start).trans hr
  cases hZ : zrun table t start with
  | none => simp [hZ] at hz
  | some z' =>
    have H := zrun_sound table m hm t start z' hZ
    have hb : embed start = blank := by
      unfold embed blank
      congr 1
      funext x
      unfold atCell start
      split <;> rfl
    rw [hb] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl
#print axioms never
end BB6.Agent25Raw43B1REE1LFM19
