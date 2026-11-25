import SweepPumping
namespace BB6.Agent10Raw108RD469
open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none
abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev E (L R : List Bool) : Z0 := ⟨4,L,R⟩
abbrev ones (n : Nat) := List.replicate n true

theorem transfer (L R : List Bool) : run0 table 6 (A (true::true::true::L) (true::R)) = some (A (true::L) (true::true::true::R)) := by rfl

theorem out_all (k r : Nat) : run0 table (6*k) (A (ones (2*k+1)) (ones (r+1))) = some (A [true] (ones (2*k+r+1))) := by
  induction k generalizing r with
  | zero => simp [run0]
  | succ k ih =>
    have h₁ := transfer (ones (2*k)) (ones r)
    have h₂ := ih (r+2)
    have h : run0 table (6+6*k) (A (ones (2*k+3)) (ones (r+1))) = some (A [true] (ones (2*k+(r+2)+1))) := join0 h₁ h₂
    rw [show 6*(k+1)=6+6*k by omega,show 2*(k+1)+1=2*k+3 by omega,show 2*(k+1)+r+1=2*k+(r+2)+1 by omega]
    exact h

theorem turn (R : List Bool) : run0 table 8 (A [true] (true::R)) = some (A [false,true] (true::true::true::R)) := by rfl
theorem start (R : List Bool) : run0 table 3 (A [false,true] (true::true::true::R)) = some (E (ones 5) R) := by rfl
theorem back_one (L R : List Bool) : run0 table 3 (E (true::true::L) (true::R)) = some (E (true::true::true::L) R) := by rfl

theorem back_all (k l : Nat) : run0 table (3*k) (E (ones (l+2)) (ones k)) = some (E (ones (k+l+2)) []) := by
  induction k generalizing l with
  | zero => simp [run0]
  | succ k ih =>
    have h := join0 (back_one (ones l) (ones k)) (ih (l+1))
    rw [show 3*(k+1)=3+3*k by omega,show k+1+l+2=k+(l+1)+2 by omega]
    exact h

theorem finish (L : List Bool) : run0 table 5 (E (true::true::L) []) = some (A (true::L) (ones 2)) := by rfl
def family (n : Nat) := A (ones (4*n+3)) (ones 2)
def cost (n : Nat) := 6*(2*n+1)+8+3+3*(4*n+3)+5

theorem entry : run0 table 14 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem positive (n : Nat) : 0 < cost n := by simp [cost]
theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h₁ := out_all (2*n+1) 1
  rw [show 2*(2*n+1)+1=4*n+3 by omega] at h₁
  have h₂ := turn (ones (4*n+3))
  have h₃ := start (ones (4*n+3))
  have h₄ := back_all (4*n+3) 3
  have h₅ := finish (ones (4*n+6))
  have h := join0 (join0 (join0 (join0 h₁ h₂) h₃) h₄) h₅
  unfold family cost
  rw [show 4*(n+1)+3=4*n+6+1 by omega]
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 14 cost entry positive growth m hm
#print axioms growth
#print axioms never
end BB6.Agent10Raw108RD469
