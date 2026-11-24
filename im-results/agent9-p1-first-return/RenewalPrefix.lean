import RenewalUnbounded

namespace BB6.Agent9Renewal
open BB6P1Unit
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000

/-- The fourth grid has 7348 bits. Its full next period is irrelevant
for the guaranteed initial shadow of this block. -/
theorem D3_period : ∃ L : Nat, D3 ∣ (2:Int)^L-1 ∧ 0<(2:Int)^L-1 := by
  let i := firstGrid.advance.advance.advance
  have hi := advance_valid _ (advance_valid _ (advance_valid _ firstGrid_valid))
  change i.valid at hi
  obtain ⟨⟨g⟩,_⟩ := hi
  have hD : i.D=D3 := by decide
  refine ⟨i.L,?_,g.Mpos⟩
  rw [←hD]
  exact g.divides

def fourthLoss (n : Nat) : Nat := 7541+4*(n.log2+1)
def fourthPrefix (n : Nat) : Nat := n-fourthLoss n

theorem fourth_margin (n : Nat) (hn : 8000≤n) :
    fourthLoss n≤n ∧ D3*(2:Int)^(fourthPrefix n)*((2:Int)^192*(n:Int)^4+6*(n:Int))<(2:Int)^n := by
  let ell := fourthLoss n
  let K := fourthPrefix n
  have hD : D3≤(2:Int)^7348 := by decide
  have hDpos : 0<D3 := by decide
  have hP := numeric_dom n hn
  have hn4 : n≤n^4 := by simpa using Nat.pow_le_pow_right (show 0<n by omega) (show 1≤4 by decide)
  have hpow : 6≤2^192 := by decide
  have h6 := Nat.mul_le_mul hpow hn4
  have h6I : 6*(n:Int)≤(2:Int)^192*(n:Int)^4 := by exact_mod_cast h6
  have hB : (2:Int)^192*(n:Int)^4+6*(n:Int)≤(2:Int)^193*(n:Int)^4 := by
    rw [show (2:Int)^193=2*(2:Int)^192 by decide,Int.mul_assoc]
    omega
  have hBp : 0≤(2:Int)^192*(n:Int)^4+6*(n:Int) := by omega
  have h2p : 0≤(2:Int)^7348 := Int.pow_nonneg (by decide : 0≤(2:Int))
  have hM := Int.mul_le_mul hD hB hBp h2p
  have hM' : D3*((2:Int)^192*(n:Int)^4+6*(n:Int))≤(2:Int)^7541*(n:Int)^4 := by
    have he : (2:Int)^7348*((2:Int)^193*(n:Int)^4)=(2:Int)^7541*(n:Int)^4 := by
      rw [←Int.mul_assoc,←Int.pow_add]
    rwa [he] at hM
  obtain ⟨hlo,hhi⟩ := log_window n (by omega)
  have h4 := Nat.pow_lt_pow_left hlo (by decide : 4≠0)
  rw [←Nat.pow_mul] at h4
  have hscale := Nat.mul_lt_mul_of_pos_left h4 (Nat.two_pow_pos 7541)
  rw [←Nat.pow_add,Nat.mul_comm (n.log2+1) 4] at hscale
  change 2^7541*n^4<2^ell at hscale
  have hscaleI : (2:Int)^7541*(n:Int)^4<(2:Int)^ell := by exact_mod_cast hscale
  have h4hi := Nat.pow_le_pow_left hhi 4
  rw [←Nat.pow_mul,Nat.mul_pow] at h4hi
  have hscalehi := Nat.mul_le_mul_left (2^7541) h4hi
  rw [←Nat.pow_add,Nat.mul_comm (n.log2+1) 4,←Nat.mul_assoc,←Nat.pow_add] at hscalehi
  change 2^ell≤2^7545*n^4 at hscalehi
  have hdom := Nat.mul_le_mul (Nat.pow_le_pow_right (show 0<2 by decide) (show 7545≤7740 by decide)) (Nat.pow_le_pow_right (show 0<n by omega) (show 4≤7 by decide))
  have hscaleP := Nat.lt_of_le_of_lt (Nat.le_trans hscalehi hdom) hP
  have hell : ell≤n := by
    by_cases h : ell≤n
    · exact h
    · have hh := Nat.pow_le_pow_right (show 0<2 by decide) (show n≤ell by omega)
      omega
  have hKell : K+ell=n := by dsimp [K,fourthPrefix,ell]; dsimp [ell] at hell; omega
  have hMsmall := Int.lt_of_le_of_lt hM' hscaleI
  have hm := Int.mul_lt_mul_of_pos_left hMsmall (show 0<(2:Int)^K by exact Int.pow_pos (by decide))
  have hmul : (2:Int)^K*(D3*((2:Int)^192*(n:Int)^4+6*(n:Int)))=D3*(2:Int)^K*((2:Int)^192*(n:Int)^4+6*(n:Int)) := by ac_rfl
  rw [hmul,←Int.pow_add,hKell] at hm
  exact ⟨hell,hm⟩

/-- Every point in the fourth-block prefix remains away from one. -/
theorem fourth_prefix_safe (n k : Nat) (hn : 8000≤n) (hk : k≤5*n+3) :
    ∀ j≤3*n+fourthPrefix n, 2≤run (7*2^n-k) (2^n+k) j := by
  obtain ⟨hfirst,p,hp,hpD,hp7,hbound⟩ := three_blocks_endpoint n k hn hk
  let q := 7*2^n-k
  let d := 2^n+k
  let q3 := q+3*n
  let d3 := run q d (3*n)
  let K := fourthPrefix n
  let C : Int := 6*(n:Int)
  let B : Int := (2:Int)^192*(n:Int)^4
  let a : Int := -(k:Int)+3*(n:Int)
  have hP := large_power n hn
  have hqk : q+k=7*2^n := by dsimp [q]; omega
  have hdq : d<q := by dsimp [d]; omega
  have hclock : (q3:Int)=7*(2:Int)^n+a := by
    have hqkI : (q:Int)+(k:Int)=7*(2:Int)^n := by exact_mod_cast hqk
    dsimp [q3,a]; push_cast; omega
  have hC : 0≤C := by dsimp [C]; omega
  have hB : 0≤B := by change 0≤(2:Int)^192*(n:Int)^4; exact Int.mul_nonneg (Int.pow_nonneg (by decide : 0≤(2:Int))) (Int.pow_nonneg (by omega : 0≤(n:Int)))
  have ha : ∀ j : Nat, j≤n → Bound (a+j) C := by intro j hj; unfold Bound a C; omega
  have hK : K≤n := by dsimp [K,fourthPrefix]; omega
  have hDpos : 0<D3 := by decide
  have hDodd : D3%2=1 := by decide
  have hsmall : D3*(2:Int)^K*(B+C)<(2:Int)^n := (fourth_margin n hn).2
  obtain ⟨L,hdiv,hM⟩ := D3_period
  intro j hj
  by_cases hj0 : j≤3*n
  · exact hfirst j hj0
  · let t := j-3*n
    have ht : t≤K := by dsimp [t,K]; omega
    have hsplit : 3*n+t=j := by dsimp [t]; omega
    have hb := (early_shadow q3 d3 n K L D3 p a C B hDpos hDodd hp hpD (run_lt q d _ hdq) hclock hdiv hM hC hB ha hbound hK hsmall t ht).1
    have hphase := orbit_range hDpos hDodd hp hpD t
    have hpow := pow_mono ht
    have hbc : 0≤B+C := by omega
    have hmul := Int.mul_le_mul_of_nonneg_right hpow hbc
    have hm := Int.mul_le_mul_of_nonneg_left (show (2:Int)^t*(B+C)-C≤(2:Int)^K*(B+C) by omega) (show 0≤D3 by omega)
    have hsmall' : D3*((2:Int)^K*(B+C))<(2:Int)^n := by simpa [Int.mul_assoc] using hsmall
    have hb' := bound_weaken hb (show D3*((2:Int)^t*(B+C)-C)≤(2:Int)^n by omega)
    have hd3P : D3≤(2:Int)^n := by
      have hD : D3≤(2:Int)^7348 := by decide
      exact Int.le_trans hD (pow_mono (show 7348≤n by omega))
    have hphaseLo := Int.mul_le_mul_of_nonneg_left (show 1≤orbit D3 p t by omega) (show 0≤7*(2:Int)^n by exact Int.mul_nonneg (by decide) (Int.pow_nonneg (by decide)))
    unfold Bound at hb'
    have hlo : D3*2≤D3*(run q3 d3 t:Int) := by omega
    have hres := Int.le_of_mul_le_mul_left hlo hDpos
    rw [←hsplit,run_add]
    exact_mod_cast hres

/-- A stronger pointwise cost bound than 4n+2 for all n≥8000. -/
theorem no_return_four_prefix (n q k : Nat) (hn : 8000≤n)
    (hclock : q+k=7*2^n-n-3) (hk : 0<k) (hcut : k≤4*n+3+fourthPrefix n) : run q 1 k≠1 := by
  have hK : fourthPrefix n≤n := by unfold fourthPrefix; omega
  have hP := large_power n hn
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
    have he : (n+3)+(k-(n+3))=k := by omega
    have hs := fourth_prefix_safe n k hn (by omega) (k-(n+3)) (by omega)
    rw [←he,run_add,hr,show q+(n+3)=7*2^n-k by omega]
    omega

#print axioms D3_period
#print axioms fourth_margin
#print axioms fourth_prefix_safe
#print axioms no_return_four_prefix
end BB6.Agent9Renewal
