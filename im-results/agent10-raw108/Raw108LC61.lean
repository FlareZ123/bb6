import SweepPumping

namespace BB6.Agent10Raw108LC61
open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- 1RB1RA_1RC0LC_0RD1LC_1LD1RE_1RF1LB_---0RA. -/
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨false,true,0⟩)
  | _,_ => none

abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev C (L R : List Bool) : Z0 := ⟨2,L,R⟩
abbrev W : List Bool := [false,true,true,false]
abbrev ones (n : Nat) := List.replicate n true

theorem ones_snoc (k : Nat) (R : List Bool) :
    ones k ++ true::R = ones (k+1) ++ R := by
  change ones k ++ ([true]++R) = ones (k+1) ++ R
  rw [← List.append_assoc]
  change (ones k++ones 1)++R = ones (k+1)++R
  rw [List.replicate_append_replicate]

theorem c_scan (k : Nat) (L R : List Bool) :
    run0 table k (C (ones k++L) R) = some (C L (ones k++R)) := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    have h₁ : run0 table 1 (C (ones (k+1)++L) R) = some (C (ones k++L) (true::R)) := by rfl
    have h := join0 h₁ (ih (true::R))
    rw [ones_snoc,show 1+k=k+1 by omega] at h
    exact h

theorem a_scan (k : Nat) (L R : List Bool) :
    run0 table (k+1) (A (true::L) (ones k++false::R)) =
      some (A (false::(ones (k+1)++L)) R) := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    have h₁ : run0 table 1 (A (true::L) (ones (k+1)++false::R)) =
      some (A (true::true::L) (ones k++false::R)) := by rfl
    have h := join0 h₁ (ih (true::L))
    rw [ones_snoc,show 1+(k+1)=k+1+1 by omega] at h
    exact h

theorem start_nonempty (L R : List Bool) :
    run0 table 2 (A (false::L) (true::R)) = some (C (true::L) (false::R)) := by rfl

theorem start_empty (L : List Bool) :
    run0 table 8 (A (false::L) []) = some (C (true::L) [false,true,true]) := by rfl

theorem turn (R : List Bool) :
    run0 table 15 (C W (true::true::R)) = some (A (true::W) (true::R)) := by rfl

def cfg (k : Nat) (R : List Bool) : Z0 := A (false::(ones (k+1)++W)) R

theorem next_nonempty (k : Nat) (R : List Bool) :
    run0 table (2+(k+2)+15+(k+2)) (cfg k (true::R)) = some (cfg (k+1) R) := by
  have h₁ := start_nonempty (ones (k+1)++W) R
  have h₂ := c_scan (k+2) W (false::R)
  have h₃ := turn (ones k++false::R)
  have h₄ := a_scan (k+1) W R
  exact join0 (join0 (join0 h₁ h₂) h₃) h₄

theorem next_empty (k : Nat) :
    run0 table (8+(k+2)+15+(k+2)) (cfg k []) = some (cfg (k+1) [true,true]) := by
  have h₁ := start_empty (ones (k+1)++W)
  have h₂ := c_scan (k+2) W [false,true,true]
  have h₃ := turn (ones k++[false,true,true])
  have h₄ := a_scan (k+1) W [true,true]
  exact join0 (join0 (join0 h₁ h₂) h₃) h₄

def family (n : Nat) : Z0 := cfg n (ones ((3-n%3)%3))
-- At entry the run of ones has length 1, and the right side is empty.
def cost (n : Nat) : Nat := (if n%3=0 then 8 else 2)+(n+2)+15+(n+2)

theorem entry : run0 table 14 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem cost_pos (n : Nat) : 0 < cost n := by unfold cost; omega

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h : n%3=0 ∨ n%3=1 ∨ n%3=2 := by omega
  rcases h with h | h | h
  · have h' : (n+1)%3=1 := by omega
    rw [cost,family,family,h,h']
    exact next_empty n
  · have h' : (n+1)%3=2 := by omega
    rw [cost,family,family,h,h']
    exact next_nonempty n [true]
  · have h' : (n+1)%3=0 := by omega
    rw [cost,family,family,h,h']
    exact next_nonempty n []

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 14 cost entry cost_pos growth m hm

#print axioms next_nonempty
#print axioms next_empty
#print axioms growth
#print axioms never
end BB6.Agent10Raw108LC61
