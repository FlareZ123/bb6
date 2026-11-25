import SweepPumping
namespace BB6.Agent1Raw60LFZeroCounter
open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none

def W : Nat → List Bool
  | 0 => [false,false,true,true]
  | n+1 => false::false::W n

def D (L R : List Bool) : Z0 := ⟨3,L,R⟩
def F (L R : List Bool) : Z0 := ⟨5,L,R⟩
def T : Nat → Nat
  | 0 => 8
  | n+1 => 2*T n+8

/-- The binary restoration loop crosses no opaque tail and returns the entire word unchanged. -/
theorem restore (n : Nat) (L R : List Bool) :
    run0 table (T n) (D (W n++L) R) = some (F (W n++L) R) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h1 : run0 table 2 (D (W (n+1)++L) R) = some (D (W n++L) (true::true::R)) := by rfl
    have h2 := ih (true::true::R)
    have h3 : run0 table 4 (F (W n++L) (true::true::R)) = some (D (W n++L) (true::false::R)) := by
      cases n <;> rfl
    have h4 := ih (true::false::R)
    have h5 : run0 table 2 (F (W n++L) (true::false::R)) = some (F (W (n+1)++L) R) := by
      cases n <;> rfl
    have H := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
    rw [show 2+T n+4+T n+2=T (n+1) by simp [T]; omega] at H
    exact H

def family (n : Nat) : Z0 := D (W n) []
def cost (n : Nat) := T n+2

theorem entry : run0 table 3 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h1 := restore n [] []
  simp only [List.append_nil] at h1
  have h2 : run0 table 2 (F (W n) []) = some (family (n+1)) := by cases n <;> rfl
  exact join0 h1 h2

theorem positive (n : Nat) : 0 < cost n := by unfold cost; omega

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 3 cost entry positive growth m hm
#print axioms restore
#print axioms growth
#print axioms never
end BB6.Agent1Raw60LFZeroCounter
