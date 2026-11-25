import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw78Growth
open BB6Coverage BB6Coverage.Agent31Pump
-- Exact table: 1RB1LB_1RC0RE_0RD1RA_1LD1RE_1LF0LB_0LA---
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | _,_ => none
abbrev O (n : Nat) := List.replicate n true
def A (m : Nat) : Z0 := ⟨0,[],false::O m⟩
def B (m : Nat) : Z0 := ⟨1,[],true::false::O m⟩
def FR (l r : Nat) : Z0 := ⟨5,false::false::O l,O r⟩
def FL (l r : Nat) : Z0 := ⟨5,false::O l,O r⟩

theorem enter (r : Nat) : run0 table 12 (A (r+4)) = some (FR 3 (r+1)) := by rfl
theorem rightStep (l r : Nat) : run0 table 13 (FR l (r+4)) = some (FR (l+3) (r+1)) := by rfl
theorem exitOne (l : Nat) : run0 table 13 (FR l 1) = some (FL (l+4) 2) := by rfl
theorem exitTwo (l : Nat) : run0 table 15 (FR l 2) = some (FL (l+2) 2) := by rfl
theorem leftStep (l r : Nat) : run0 table 12 (FL (l+2) r) = some (FL l (r+2)) := by rfl
theorem oddExit (r : Nat) : run0 table 2 (FL 1 r) = some (B r) := by rfl
theorem evenExit (r : Nat) : run0 table 1 (FL 0 r) = some (A r) := by rfl
theorem mid (r : Nat) : run0 table 11 (B (r+4)) = some (FR 4 (r+1)) := by rfl

theorem rightSweep (k l r : Nat) :
    run0 table (13*k) (FR l (3*k+r+1)) = some (FR (l+3*k) (r+1)) := by
  induction k generalizing l with
  | zero => simp [run0]
  | succ k ih =>
    have h1 := rightStep l (3*k+r)
    have h2 := ih (l+3)
    have h := join0 h1 h2
    rw [show 3*k+r+4=3*(k+1)+r+1 by omega,
        show l+3+3*k=l+3*(k+1) by omega,
        show 13+13*k=13*(k+1) by omega] at h
    exact h

theorem leftSweep (k l r : Nat) :
    run0 table (12*k) (FL (2*k+l) r) = some (FL l (r+2*k)) := by
  induction k generalizing r with
  | zero => simp [run0]
  | succ k ih =>
    have h1 := leftStep (2*k+l) r
    have h2 := ih (r+2)
    have h := join0 h1 h2
    rw [show 2*k+l+2=2*(k+1)+l by omega,
        show r+2+2*k=r+2*(k+1) by omega,
        show 12+12*k=12*(k+1) by omega] at h
    exact h

def family (n : Nat) : Z0 := A (12*n+10)
def cost (n : Nat) : Nat := 372*n+473

theorem entry : run0 table 111 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h1 := enter (12*n+6)
  have h2 := rightSweep (4*n+2) 3 0
  have h3 := exitOne (12*n+9)
  have h4 := leftSweep (6*n+6) 1 2
  have h5 := oddExit (12*n+14)
  rw [show 12*n+6+4=12*n+10 by omega,show 12*n+6+1=12*n+7 by omega] at h1
  rw [show 3*(4*n+2)+0+1=12*n+7 by omega,show 3+3*(4*n+2)=12*n+9 by omega] at h2
  rw [show 12*n+9+4=12*n+13 by omega] at h3
  rw [show 2*(6*n+6)+1=12*n+13 by omega,show 2+2*(6*n+6)=12*n+14 by omega] at h4
  have hA := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  have h6 := mid (12*n+10)
  have h7 := rightSweep (4*n+3) 4 1
  have h8 := exitTwo (12*n+13)
  have h9 := leftSweep (6*n+7) 1 2
  have h10 := oddExit (12*n+16)
  rw [show 12*n+10+4=12*n+14 by omega,show 12*n+10+1=12*n+11 by omega] at h6
  rw [show 3*(4*n+3)+1+1=12*n+11 by omega,show 4+3*(4*n+3)=12*n+13 by omega] at h7
  rw [show 12*n+13+2=12*n+15 by omega] at h8
  rw [show 2*(6*n+7)+1=12*n+15 by omega,show 2+2*(6*n+7)=12*n+16 by omega] at h9
  have hB := join0 (join0 (join0 (join0 h6 h7) h8) h9) h10
  have h11 := mid (12*n+12)
  have h12 := rightSweep (4*n+4) 4 0
  have h13 := exitOne (12*n+16)
  have h14 := leftSweep (6*n+10) 0 2
  have h15 := evenExit (12*n+22)
  rw [show 12*n+12+4=12*n+16 by omega,show 12*n+12+1=12*n+13 by omega] at h11
  rw [show 3*(4*n+4)+0+1=12*n+13 by omega,show 4+3*(4*n+4)=12*n+16 by omega] at h12
  rw [show 12*n+16+4=12*n+20 by omega] at h13
  rw [show 2*(6*n+10)+0=12*n+20 by omega,show 2+2*(6*n+10)=12*n+22 by omega] at h14
  have hC := join0 (join0 (join0 (join0 h11 h12) h13) h14) h15
  have h := join0 (join0 hA hB) hC
  have hcost : (12+13*(4*n+2)+13+12*(6*n+6)+2)+(11+13*(4*n+3)+15+12*(6*n+7)+2)+(11+13*(4*n+4)+13+12*(6*n+10)+1)=cost n := by unfold cost;omega
  rw [hcost,show 12*n+22=12*(n+1)+10 by omega] at h
  exact h

theorem cost_pos (n : Nat) : 0 < cost n := by unfold cost;omega
#print axioms entry
#print axioms growth
end BB6.Agent8Raw78Growth
