import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw69Growth
open BB6Coverage BB6Coverage.Agent31Pump
-- Exact table: 1RB---_1RC0LC_0RD0LF_1LD1RE_0RA0LB_1LB1RA
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none

def P : List Bool := [false,true,false,true,true]
def A (k : Nat) (R : List Bool) : Z0 := ⟨0,false::(rep P k ++ [true]),R⟩
def F (k : Nat) (R : List Bool) : Z0 := ⟨5,rep P k ++ [true],R⟩

theorem fStep (k : Nat) (R : List Bool) :
    run0 table 9 (F (k+1) R) = some (F k ([false,false,false,true,true] ++ R)) := by rfl
theorem fBase (R : List Bool) : run0 table 1 (F 0 (false::R)) = some (A 0 R) := by rfl
theorem countStart (k : Nat) (R : List Bool) :
    run0 table 13 (A k ([false,false,true,true] ++ R)) = some (F k ([false,false,false,true,false] ++ R)) := by rfl
theorem pop (k : Nat) (R : List Bool) :
    run0 table 5 (A k ([false,false,true,false,false] ++ R)) = some (A (k+1) R) := by rfl
theorem enter (k : Nat) : run0 table 9 (A k []) = some (F k [false,false,false,true]) := by rfl
theorem finish (k : Nat) : run0 table 5 (A k [false,false,true]) = some (A (k+1) []) := by rfl

def fCost : Nat → Nat
  | 0 => 1
  | k+1 => 9 + fCost k + 13 + fCost k + 5

theorem resolveF (k : Nat) (R : List Bool) :
    run0 table (fCost k) (F k (false::R)) = some (A k R) := by
  induction k generalizing R with
  | zero => exact fBase R
  | succ k ih =>
    have h1 := fStep k (false::R)
    have h2 := ih ([false,false,true,true,false] ++ R)
    have h3 := countStart k (false::R)
    have h4 := ih ([false,false,true,false,false] ++ R)
    have h5 := pop k R
    exact join0 (join0 (join0 (join0 h1 h2) h3) h4) h5

def family (n : Nat) : Z0 := A (n+1) []
def cost (n : Nat) : Nat := 9 + fCost (n+1) + 5

theorem entry : run0 table 42 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  exact join0 (join0 (enter (n+1)) (resolveF (n+1) [false,false,true])) (finish (n+1))
theorem cost_pos (n : Nat) : 0 < cost n := by unfold cost; omega
theorem fCost_formula (k : Nat) : fCost k + 27 = 28 * 2^k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [fCost, Nat.pow_succ]; omega

theorem cost_formula (n : Nat) : cost n + 13 = 28 * 2^(n+1) := by
  unfold cost
  have h := fCost_formula (n+1)
  omega
#print axioms entry
#print axioms growth
#print axioms cost_formula
end BB6.Agent8Raw69Growth
