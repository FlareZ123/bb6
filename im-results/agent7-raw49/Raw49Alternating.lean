import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6.Agent7Raw49Alternating
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | _,_ => none

def F (l r : List Bool) : Z0 := ⟨5,l,r⟩
def L : Nat → List Bool
  | 0 => []
  | n+1 => false :: true :: L n
def R : Nat → List Bool
  | 0 => [true]
  | n+1 => true :: false :: R n

def family (n : Nat) : Z0 := F [false] (R (2*n+3))

theorem rfirst (k : Nat) : run0 table 4 (F [false] (R (k+1))) = some (F (false::false::L 1) (R k)) := by rfl

theorem rstep (j k : Nat) : run0 table 4 (F (false::false::L (j+1)) (R (k+1))) = some (F (false::false::L (j+2)) (R k)) := by rfl

theorem rscan (n j : Nat) : run0 table (4*n) (F (false::false::L (j+1)) (R n)) = some (F (false::false::L (j+1+n)) (R 0)) := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    have h := join0 (rstep j n) (ih (j+1))
    rw [show 4+4*n=4*(n+1) by omega,show j+1+1+n=j+1+(n+1) by omega] at h
    exact h

theorem rlast (j : Nat) : run0 table 4 (F (false::false::L (j+1)) (R 0)) = some (F (false::false::L (j+2)) []) := by rfl
theorem turn (j : Nat) : run0 table 4 (F (false::false::L (j+1)) []) = some (F (L (j+2)) (R 0)) := by rfl

theorem lstep (j k : Nat) : run0 table 16 (F (L (j+2)) (R k)) = some (F (L (j+1)) (R (k+1))) := by cases k <;> rfl
theorem lscan (n k : Nat) : run0 table (16*n) (F (L (n+1)) (R k)) = some (F (L 1) (R (k+n))) := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    have h := join0 (lstep n k) (ih (k+1))
    rw [show 16+16*n=16*(n+1) by omega,show k+1+n=k+(n+1) by omega] at h
    exact h

theorem llast (k : Nat) : run0 table 16 (F (L 1) (R k)) = some (F [false] (R (k+1))) := by cases k <;> rfl

theorem epoch (k : Nat) : run0 table (20*k+60) (F [false] (R (k+1))) = some (F [false] (R (k+3))) := by
  have h := join0 (rfirst k) (rscan k 0)
  simp only [Nat.zero_add] at h
  rw [show 1+k=k+1 by omega] at h
  have h := join0 h (rlast k)
  have h := join0 h (turn (k+1))
  have h := join0 h (lscan (k+2) 0)
  simp only [Nat.zero_add] at h
  have h := join0 h (llast (k+2))
  rw [show 4+4*k+4+4+16*(k+2)+16=20*k+60 by omega] at h
  exact h

theorem entry : run0 table 70 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem growth (n : Nat) : run0 table (40*n+100) (family n) = some (family (n+1)) := by
  have h := epoch (2*n+2)
  rw [show 20*(2*n+2)+60=40*n+100 by omega,show 2*n+2+1=2*n+3 by omega,show 2*n+2+3=2*(n+1)+3 by omega] at h
  exact h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 70 (fun n => 40*n+100) entry (by omega) growth m hm
#print axioms never
end BB6.Agent7Raw49Alternating
