import SweepPumping
import BlankDelayKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6.Agent7Raw49Sweep
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent13BlankDelay

inductive Kind where
  | direct | viaA | viaB | viaE
  deriving DecidableEq, Repr

def target : Kind → Fin 6
  | .direct => 2
  | .viaA => 0
  | .viaB => 1
  | .viaE => 4

def table (kind : Kind) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => if kind = .viaA then some (some ⟨false,true,2⟩) else none
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => if kind = .viaB then some (some ⟨false,true,2⟩) else none
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,target kind⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,true => if kind = .viaE then some (some ⟨false,true,2⟩) else none
  | _,_ => none

def C (l r : List Bool) : Z0 := ⟨2,l,r⟩
def D (l r : List Bool) : Z0 := ⟨3,l,r⟩
def z : Nat → List Bool
  | 0 => []
  | n+1 => false :: z n
def o : Nat → List Bool
  | 0 => []
  | n+1 => true :: o n

def family (n : Nat) : Z0 := C [true,true,true] (o (2*n+1))

theorem pair (kind : Kind) (k : Nat) (L R : List Bool) :
    run0 (table kind) 2 (C (true :: z k ++ L) (true :: true :: R)) =
      some (C (true :: z (k+2) ++ L) R) := by cases kind <;> rfl

theorem pairs (kind : Kind) (n k : Nat) (L : List Bool) :
    run0 (table kind) (2*n) (C (true :: z k ++ L) (o (2*n+1))) =
      some (C (true :: z (k+2*n) ++ L) [true]) := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    have h := join0 (pair kind k L (o (2*n+1))) (ih (k+2))
    rw [show 2+2*n=2*(n+1) by omega,show k+2+2*n=k+2*(n+1) by omega] at h
    rw [show 2*(n+1)+1=(2*n+1)+2 by omega]
    exact h

theorem scanD (kind : Kind) (n k : Nat) (L : List Bool) :
    run0 (table kind) n (D (z n ++ L) (o k)) = some (D L (o (k+n))) := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    have h := ih (k+1)
    rw [show k+1+n=k+(n+1) by omega] at h
    exact h

theorem lastC (kind : Kind) (k : Nat) :
    run0 (table kind) 3 (C (true :: z k ++ [true,true]) [true]) =
      some (D (z (k+4) ++ [true,true]) []) := by cases kind <;> rfl

theorem turnD (kind : Kind) (k : Nat) :
    run0 (table kind) 1 (D [true,true] (o (k+1))) = some (C [true,true,true] (o k)) := by rfl

theorem growth (kind : Kind) (n : Nat) : run0 (table kind) (4*n+8) (family n) = some (family (n+1)) := by
  have hC := pairs kind n 0 [true,true]
  simp only [Nat.zero_add] at hC
  have h := join0 hC (lastC kind (2*n))
  have hD := scanD kind (2*n+4) 0 [true,true]
  simp only [Nat.zero_add] at hD
  have h := join0 h hD
  have h := join0 h (turnD kind (2*n+3))
  rw [show 2*n+3+(2*n+4)+1=4*n+8 by omega] at h
  unfold family
  rw [show 2*(n+1)+1=2*n+3 by omega]
  exact h

theorem entry (kind : Kind) : run0 (table kind) 6 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem never (kind : Kind) (m : Machine) (hm : compatible (table kind) m) : NeverHalts m :=
  never_of_growth (table kind) family 6 (fun n => 4*n+8) (entry kind) (by omega) (growth kind) m hm
#print axioms growth
#print axioms never
end BB6.Agent7Raw49Sweep
