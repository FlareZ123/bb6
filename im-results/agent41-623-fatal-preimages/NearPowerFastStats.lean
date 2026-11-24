import NearPowerDrain

namespace BB6.Agent41NearPower
open BB6.Agent49CorrectionGrowth

/-- Used only in the short-tail fallback. -/
def blockVal (C k : Nat) (w : Int) : Nat := (((C:Int)*3^k+w)/2).toNat

def directStats (C k : Nat) (w : Int) : Int × Nat :=
  (drift (blockVal C k w),excess (blockVal C k w))

def cheapSafe (k : Nat) (w : Int) : Prop := w.natAbs.log2+2≤k
instance (k : Nat) (w : Int) : Decidable (cheapSafe k w) := by unfold cheapSafe; infer_instance

def fixed (w : Int) : Prop := w=-3 ∨ w=-1 ∨ w=1
instance (w : Int) : Decidable (fixed w) := by unfold fixed; infer_instance

def cycling (w : Int) : Prop := w=-2 ∨ w=0
instance (w : Int) : Decidable (cycling w) := by unfold cycling; infer_instance

/-- A fuel-bounded evaluator which computes the actual exact statistic. Fuel
    exhaustion uses direct computation, so every fuel value is sound. -/
def fastStatsFuel (C : Nat) : Nat → Nat → Int → Int × Nat
  | 0,k,w => directStats C k w
  | f+1,k,w =>
    if k≤2 then directStats C k w
    else if fixed w then
      let c := directStats C 2 w
      (c.1+(↑(k-2):Int)*driftCharge (residue w).toNat,
       c.2+(k-2)*excessCharge (residue w).toNat)
    else if cycling w ∧ k%2=0 then
      let c := directStats C 2 w
      (c.1,c.2+2*((k-2)/2))
    else if cheapSafe k w ∨ cycling w then
      let c := fastStatsFuel C f (k-1) (residualStep w)
      (c.1+driftCharge (residue w).toNat,c.2+excessCharge (residue w).toNat)
    else directStats C k w

def fastStats (C k : Nat) (w : Int) : Int×Nat := fastStatsFuel C (w.natAbs.log2+5) k w

private theorem blockVal_eq (C k b : Nat) (w : Int)
    (h : 2*(b:Int)=(C:Int)*3^k+w) : blockVal C k w=b := by
  unfold blockVal
  omega

private theorem intPowOdd (k : Nat) : (3:Int)^k%2=1 := by
  induction k with
  | zero => decide
  | succ k ih => rw [Int.pow_succ]; omega

private theorem base_rep (C k b : Nat) (w : Int) (hC : 0<C) (hw : -3≤w)
    (h : 2*(b:Int)=(C:Int)*3^k+w) :
    2*(blockVal C 2 w:Int)=(C:Int)*3^2+w := by
  have hodd := intPowOdd k
  have hmod := Int.mul_emod (C:Int) ((3:Int)^k) 2
  rw [hodd] at hmod
  have hc : ((C:Int)*3^k)%2=(C:Int)%2 := by omega
  unfold blockVal
  change 2*((((C:Int)*9+w)/2).toNat:Int)=(C:Int)*9+w
  omega

private theorem pow_margin (k : Nat) (w : Int) (h : cheapSafe k w) : w.natAbs+2≤3^k := by
  unfold cheapSafe at h
  by_cases hz : w.natAbs=0
  · have h1 := Nat.pow_le_pow_right (show 0<3 by decide) (show 1≤k by omega)
    simp at h1
    omega
  · have hl := (Nat.log2_lt hz).mp (show w.natAbs.log2<w.natAbs.log2+1 by omega)
    have h1 : 2^(w.natAbs.log2+2)≤2^k := Nat.pow_le_pow_right (by decide) h
    have h2 : 2^k≤3^k := Nat.pow_le_pow_left (by decide) k
    rw [Nat.pow_succ] at h1
    have hp : 0<2^(w.natAbs.log2+1) := Nat.pow_pos (by decide)
    omega

private theorem cheap_pos (C k b : Nat) (w : Int) (hC : 0<C)
    (h : 2*(b:Int)=(C:Int)*3^k+w) (hs : cheapSafe k w) : 0<b := by
  have hp := pow_margin k w hs
  have h3 : (3:Int)^k≤(C:Int)*3^k := by
    have hnn : 0≤(3:Int)^k := by exact Int.le_of_lt (Int.pow_pos (by decide))
    have hm := Int.mul_le_mul_of_nonneg_right (show (1:Int)≤C by omega) hnn
    simpa using hm
  have hp' : (w.natAbs:Int)+2≤(3:Int)^k := by
    have hh : ((3^k:Nat):Int) = (3:Int)^k := Int.natCast_pow 3 k
    rw [←hh]
    omega
  omega

private theorem cycle_pos (C k b : Nat) (w : Int) (hC : 0<C) (hk : 2<k)
    (h : 2*(b:Int)=(C:Int)*3^k+w) (hw : cycling w) : 0<b := by
  have hpow := Nat.pow_le_pow_right (show 0<3 by decide) (show 2≤k by omega)
  have h3 : (9:Int)≤3^k := by
    have hh : ((3^k:Nat):Int) = (3:Int)^k := Int.natCast_pow 3 k
    change 9≤3^k at hpow
    rw [←hh]
    omega
  have hm := Int.mul_le_mul_of_nonneg_right (show (1:Int)≤C by omega) (show 0≤(3:Int)^k by omega)
  simp only [Int.one_mul] at hm
  unfold cycling at hw
  omega

theorem fastStatsFuel_correct (C f : Nat) (hC : 0<C) :
    ∀ (k : Nat) (w : Int) (b : Nat), 2*(b:Int)=(C:Int)*3^k+w → fastStatsFuel C f k w=(drift b,excess b) := by
  induction f with
  | zero =>
    intro k w b h
    simp [fastStatsFuel,directStats,blockVal_eq C k b w h]
  | succ f ih =>
    intro k w b h
    rw [fastStatsFuel]
    split
    · simp [directStats,blockVal_eq C k b w h]
    next hk =>
      split
      next hf =>
        have hw : -3≤w := by unfold fixed at hf; omega
        have hs : residualStep w=w := by
          unfold fixed at hf
          rcases hf with he|he|he <;> subst w <;> decide
        have hbase := base_rep C k b w hC hw h
        have hk' : k-2+2=k := by omega
        have ht := fixed_tail C (k-2) b (blockVal C 2 w) w hC hw hs (by rw [hk']; exact h) hbase
        simp only [directStats]
        exact Prod.ext (by simpa using ht.1.symm) (by simpa using ht.2.symm)
      next hnf =>
        split
        next hc =>
          have hw : -3≤w := by unfold cycling at hc; omega
          have hbase := base_rep C k b w hC hw h
          have hk' : 2*((k-2)/2)+2=k := by omega
          have ht := cycle_tail C ((k-2)/2) b (blockVal C 2 w) w hC hc.1 (by rw [hk']; exact h) hbase
          simp only [directStats]
          exact Prod.ext ht.1.symm ht.2.symm
        next hnc =>
          split
          next hs =>
            have hp : 0<b := by
              rcases hs with hsafe|hcyc
              · exact cheap_pos C k b w hC h hsafe
              · exact cycle_pos C k b w hC (by omega) h hcyc
            have hk' : k-1+1=k := by omega
            obtain ⟨hr,hn⟩ := residual_step C (k-1) b w hp (by rw [hk']; exact h)
            have hi := ih (k-1) (residualStep w) (nextBlock b) hn
            have hj := nextBlock_stats b hp
            have hm : b%3=(residue w).toNat := by omega
            rw [hm] at hj
            simp only [hi]
            exact Prod.ext hj.1.symm hj.2.symm
          · simp [directStats,blockVal_eq C k b w h]

theorem fastStats_correct (C k b : Nat) (w : Int) (hC : 0<C)
    (h : 2*(b:Int)=(C:Int)*3^k+w) : fastStats C k w=(drift b,excess b) :=
  fastStatsFuel_correct C _ hC k w b h

#print axioms fastStatsFuel_correct
#print axioms fastStats_correct
end BB6.Agent41NearPower
