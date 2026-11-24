import NearPowerFastStats

namespace BB6.Agent41NearPower
open BB6.Agent49CorrectionGrowth

def stable (w : Int) : Prop := fixed w ∨ cycling w

def pairJ (w : Int) : Int := driftCharge (residue w).toNat+driftCharge (residue (residualStep w)).toNat

def pairE (w : Int) : Nat := excessCharge (residue w).toNat+excessCharge (residue (residualStep w)).toNat

private theorem stable_bounds {w : Int} (h : stable w) : -3≤w ∧ w≤1 := by
  unfold stable fixed cycling at h
  omega

private theorem stable_next {w : Int} (h : stable w) : stable (residualStep w) ∧ residualStep (residualStep w)=w := by
  unfold stable fixed cycling at h
  rcases h with ((h|h|h)|(h|h)) <;> subst w <;> unfold stable fixed cycling <;> decide

private theorem positive_rep (C k b : Nat) (w : Int) (hC : 5≤C) (hw : -3≤w)
    (h : 2*(b:Int)=(C:Int)*3^k+w) : 0<b := by
  have hp : (1:Int)≤3^k := by have hh : (0:Int)<3^k := Int.pow_pos (by decide); omega
  have hm := Int.mul_le_mul_of_nonneg_left hp (show 0≤(C:Int) by omega)
  simp only [Int.mul_one] at hm
  omega

/-- Pump an arbitrary stable two-digit residual tail above a positive base.
The leading coefficient need not be small, so it may itself contain an
independent exponential term. -/
theorem pair_pump (C n b c : Nat) (w : Int) (hC : 5≤C) (hw : stable w)
    (hb : 2*(b:Int)=(C:Int)*3^(2*n)+w) (hc : 2*(c:Int)=(C:Int)+w) :
    drift b=drift c+(n:Int)*pairJ w ∧ excess b=excess c+n*pairE w := by
  induction n generalizing b with
  | zero =>
    have he : b=c := by simp at hb; omega
    subst b
    simp
  | succ n ih =>
    have hp := positive_rep C (2*(n+1)) b w hC (stable_bounds hw).1 hb
    have he : 2*(b:Int)=(C:Int)*3^((2*n+1)+1)+w := by simpa only [show 2*(n+1)=2*n+1+1 by omega] using hb
    obtain ⟨hr,hn⟩ := residual_step C (2*n+1) b w hp he
    have hstable := stable_next hw
    have hp' := positive_rep C (2*n+1) (nextBlock b) (residualStep w) hC (stable_bounds hstable.1).1 hn
    obtain ⟨hr',hn'⟩ := residual_step C (2*n) (nextBlock b) (residualStep w) hp' hn
    rw [hstable.2] at hn'
    have hrec := ih (nextBlock (nextBlock b)) hn'
    have hst := nextBlock_stats b hp
    have hst' := nextBlock_stats (nextBlock b) hp'
    have hm : b%3=(residue w).toNat := by omega
    have hm' : nextBlock b%3=(residue (residualStep w)).toNat := by omega
    rw [hm] at hst
    rw [hm'] at hst'
    constructor
    · rw [hst.1,hst'.1,hrec.1,Int.natCast_succ,Int.add_mul]
      unfold pairJ
      omega
    · rw [hst.2,hst'.2,hrec.2,Nat.succ_mul]
      unfold pairE
      omega

/-- Two arbitrary nested exponential terms can be merged into the positive
coefficient for the exact low-residual pump. -/
theorem nested_pump (C k n b c : Nat) (W w : Int) (hw : stable w)
    (hpos : 5≤(C:Int)*3^k+W)
    (hb : 2*(b:Int)=(C:Int)*3^(k+2*n)+W*3^(2*n)+w)
    (hc : 2*(c:Int)=(C:Int)*3^k+W+w) :
    drift b=drift c+(n:Int)*pairJ w ∧ excess b=excess c+n*pairE w := by
  let V := ((C:Int)*3^k+W).toNat
  have hV : 5≤V := by dsimp [V]; omega
  have hv : (V:Int)=(C:Int)*3^k+W := by dsimp [V]; omega
  apply pair_pump V n b c w hV hw
  · rw [hv,Int.add_mul,Int.mul_assoc,←Int.pow_add]; exact hb
  · rw [hv]; exact hc

#print axioms pair_pump
#print axioms nested_pump
end BB6.Agent41NearPower
