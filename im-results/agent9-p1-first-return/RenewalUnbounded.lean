import RenewalMany
import RenewalFourN

namespace BB6.Agent9Renewal
open BB6P1Unit
set_option maxHeartbeats 2000000

/-- An entirely explicit threshold for B renewal blocks. The computation
uses only the period update, polynomial error coefficients and log2. -/
def criticalThreshold (B : Nat) : Nat :=
  max 14 (max (coefficientThreshold (B+5) 1) (manyThreshold B firstGrid (B+4) (B+4) 1))

theorem critical_power (B n : Nat) (hn : criticalThreshold B≤n) : (B+5)*n<2^n := by
  have h1 : max (coefficientThreshold (B+5) 1) (manyThreshold B firstGrid (B+4) (B+4) 1)≤n := Nat.le_trans (Nat.le_max_right _ _) hn
  have h2 := coefficient_dom (B+5) 1 n (Nat.le_trans (Nat.le_max_left _ _) h1)
  simpa using h2

theorem initial_doubling_general (n q j : Nat) (hq : 4*2^n<q+1)
    (hj : j≤n+2) : run q 1 j=2^j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hp := Nat.pow_le_pow_right (show 0<2 by decide) hj
    rw [show 2^(n+2)=4*2^n by rw [Nat.pow_add]; simp; omega] at hp
    have hp2 : 2*2^j=2^(j+1) := by rw [Nat.pow_succ]; ac_rfl
    rw [run,unit,ih (by omega),hp2,Nat.mod_eq_of_lt (by omega)]

/-- For every B and every n above the explicit threshold, the critical
running-modulus return cannot have length at most (B+1)n+3. -/
theorem no_return_many (B n q k : Nat) (hn : criticalThreshold B≤n)
    (hclock : q+k=7*2^n-n-3) (hk : 0<k) (hcut : k≤(B+1)*n+3) : run q 1 k≠1 := by
  have hn14 : 14≤n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hP := critical_power B n hn
  have hBn : B*n+5*n<2^n := by simpa [Nat.add_mul] using hP
  have hcut' : k≤B*n+n+3 := by simpa [Nat.add_mul] using hcut
  have hq : 4*2^n<q+1 := by omega
  by_cases h0 : k≤n+2
  · rw [initial_doubling_general n q k hq h0]
    have hp : 2≤2^k := Nat.pow_le_pow_right (show 0<2 by decide) (show 1≤k by omega)
    omega
  · have hr : run q 1 (n+3)=2^n+k := by
      rw [show n+3=n+2+1 by omega,run,unit,initial_doubling_general n q (n+2) hq (by omega)]
      rw [show 2*2^(n+2)=8*2^n by rw [Nat.pow_add]; simp; omega]
      rw [show q+(n+2)+1=7*2^n-k by omega]
      rw [Nat.mod_eq_sub_mod (by omega),show 8*2^n-(7*2^n-k)=2^n+k by omega,Nat.mod_eq_of_lt (by omega)]
    let q0 := 7*2^n-k
    let d0 := 2^n+k
    have hq0 : q0+k=7*2^n := by dsimp [q0]; omega
    have hclock0 : (q0:Int)=7*(2:Int)^n-(k:Int) := by
      have h : (q0:Int)+(k:Int)=7*(2:Int)^n := by exact_mod_cast hq0
      omega
    have hd0q0 : d0<q0 := by dsimp [d0,q0]; omega
    have hcutI : (k:Int)≤(B:Int)*n+n+3 := by exact_mod_cast hcut'
    have hC : ((B+4:Nat):Int)*n=(B:Int)*n+4*n := by push_cast; grind only
    have ha : ∀ j : Nat, j≤B*n → Bound (-(k:Int)+j) (((B+4:Nat):Int)*n) := by
      intro j hj
      have hjI : (j:Int)≤(B:Int)*n := by exact_mod_cast hj
      unfold Bound
      rw [hC]
      omega
    have hinit : Bound (firstGrid.D*(d0:Int)-7*(2:Int)^n*1) (firstGrid.D*(((B+4:Nat):Int)*(n:Int)^1)) := by
      have he : (d0:Int)=(2:Int)^n+(k:Int) := by dsimp [d0]
      rw [he]
      change Bound (7*((2:Int)^n+k)-7*(2:Int)^n*1) (7*(((B+4:Nat):Int)*(n:Int)^1))
      unfold Bound
      rw [Int.pow_one,hC]
      omega
    have hdom : manyThreshold B firstGrid (B+4) (B+4) 1≤n := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) hn)
    have he : n+3+(k-(n+3))=k := by omega
    have hrem : k-(n+3)≤B*n := by omega
    rw [←he,run_add,hr,show q+(n+3)=q0 by dsimp [q0]; omega]
    by_cases hz : k-(n+3)=0
    · simp [hz,run]
      omega
    · have hs := many_blocks B firstGrid (B+4) (B+4) 1 firstGrid_valid (by omega) (by decide) n q0 d0 1 (-(k:Int)) (by omega) hdom (by decide) (by decide) (by decide) hd0q0 hclock0 ha hinit (k-(n+3)) (by omega) hrem
      change 2≤run q0 (2^n+k) (k-(n+3)) ∧ _ at hs
      omega

#print axioms no_return_many
end BB6.Agent9Renewal
