import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw55Sweep
open BB6Coverage BB6Coverage.Agent31Pump

inductive Kind where
  | viaA | viaB | direct
  deriving DecidableEq, Repr

def table (kind : Kind) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,4⟩)
  | 4,true => some (some (match kind with
      | .viaA => ⟨false,false,0⟩
      | .viaB => ⟨true,false,1⟩
      | .direct => ⟨true,true,2⟩))
  | _,_ => none

def C (l r : List Bool) : Z0 := ⟨2,l,r⟩
def D (l r : List Bool) : Z0 := ⟨3,l,r⟩
def E (l r : List Bool) : Z0 := ⟨4,l,r⟩
def z : Nat → List Bool
  | 0 => []
  | n+1 => false :: z n
def o : Nat → List Bool
  | 0 => []
  | n+1 => true :: o n

/-- Erase n+1 consecutive ones to the right, retaining an arbitrary left tail. -/
theorem scanC (kind : Kind) (n k : Nat) (L : List Bool) :
    run0 (table kind) (n+1) (C (true :: z k ++ L) (o n)) =
      some (C (false :: z (k+n+1) ++ L) []) := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    have h := ih (k+1)
    rw [show k+1+n+1=k+(n+1)+1 by omega] at h
    exact h

/-- Refill a zero interval by ones moving left. -/
theorem scanD (kind : Kind) (n k : Nat) (L : List Bool) :
    run0 (table kind) n (D (z n ++ L) (o k)) = some (D L (o (k+n))) := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    have h := ih (k+1)
    rw [show k+1+n=k+(n+1) by omega] at h
    exact h

/-- Common exact right-turn, refill and left-turn epoch, with arbitrary left tail. -/
theorem finish (kind : Kind) (n : Nat) (L : List Bool) :
    run0 (table kind) (2*n+6) (C (true :: true :: L) (o n)) =
      some (E (true :: false :: L) (o (n+2))) := by
  have h1 := scanC kind n 0 (true :: L)
  simp only [z, Nat.zero_add] at h1
  have h2 : run0 (table kind) 1 (C (false :: z (n+1) ++ true :: L) []) =
      some (D (z (n+3) ++ true :: L) []) := by rfl
  have h3 := scanD kind (n+3) 0 (true :: L)
  have h3' : run0 (table kind) (n+3) (D (z (n+3) ++ true :: L) []) = some (D (true :: L) (o (n+3))) := by
    rw [Nat.zero_add] at h3
    exact h3
  have h4 : run0 (table kind) 1 (D (true :: L) (o (n+3))) =
      some (E (true :: false :: L) (o (n+2))) := by rfl
  have h := join0 (join0 (join0 h1 h2) h3') h4
  rw [show n+1+1+(n+3)+1=2*n+6 by omega] at h
  exact h

def family (kind : Kind) (k : Nat) : Z0 :=
  match kind with
  | .viaA => E (true :: false :: o (k+1)) (o (k+1))
  | .viaB => E [true,false,true] (o (2*k+1))
  | .direct => E (true :: z (k+1) ++ [true]) (o (k+1))

def cost (kind : Kind) (k : Nat) : Nat :=
  match kind with
  | .viaA => 2*k+9
  | .viaB => 4*k+10
  | .direct => 2*k+7

theorem first (kind : Kind) : run0 (table kind) 6 ⟨0,[],[]⟩ = some (family kind 0) := by
  cases kind <;> rfl

theorem growth (kind : Kind) (k : Nat) :
    run0 (table kind) (cost kind k) (family kind k) = some (family kind (k+1)) := by
  cases kind with
  | viaA =>
    have h1 : run0 (table .viaA) 3 (family .viaA k) =
      some (C (true :: true :: true :: o (k+1)) (o k)) := by rfl
    have h := join0 h1 (finish .viaA k (true :: o (k+1)))
    rw [show 3+(2*k+6)=2*k+9 by omega] at h
    exact h
  | viaB =>
    have h1 : run0 (table .viaB) 2 (family .viaB k) =
      some (C [true,true,true] (o (2*k+1))) := by rfl
    have h := join0 h1 (finish .viaB (2*k+1) [true])
    rw [show 2+(2*(2*k+1)+6)=4*k+10 by omega,
        show 2*k+1+2=2*(k+1)+1 by omega] at h
    exact h
  | direct =>
    have h1 : run0 (table .direct) 1 (family .direct k) =
      some (C (true :: true :: z (k+1) ++ [true]) (o k)) := by rfl
    have h := join0 h1 (finish .direct k (z (k+1) ++ [true]))
    rw [show 1+(2*k+6)=2*k+7 by omega] at h
    exact h

theorem never (kind : Kind) (m : Machine) (hm : compatible (table kind) m) :
    NeverHalts m :=
  never_of_growth (table kind) (family kind) 6 (cost kind) (first kind)
    (by intro k; cases kind <;> simp only [cost] <;> omega) (growth kind) m hm

#print axioms first
#print axioms finish
#print axioms growth
#print axioms never
end BB6.Agent25Raw55Sweep
