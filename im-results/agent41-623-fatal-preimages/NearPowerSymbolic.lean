import NearPowerSymbolicStats
import NearPowerTree

namespace BB6.Agent41NearPower
open BB6.Agent49CorrectionGrowth

/-- Candidate trace generator. Only symStats, not the generator, is trusted. -/
def genStats : Nat → Aff → Int → Int → StatsCert
  | 0,_,_,_ => .fixed
  | f+1,k,W,B =>
    if W=0 ∧ fixed B then .fixed
    else if W=0 ∧ cycling B ∧ modEq k 2 0=true then .cycle
    else if W≠0 ∧ stable B then .pump (genStats f (k-(2:Int)*an) 0 (W+B))
    else .step (genStats f (k-ac 1) (W/3) (residualStep B))

def symEval (C : Nat) (k w : Aff) : Option (Aff×Aff) :=
  if w.b=0 then symStats C k w.a w.c (genStats 512 k w.a w.c) else none

theorem symEval_sound {C : Nat} {k w : Aff} {s : Aff×Aff} (hC : 0<C)
    (h : symEval C k w=some s) (n b : Nat)
    (hr : 2*(b:Int)=(C:Int)*3^(k.eval n).toNat+w.eval n) : StatsRep s n b := by
  unfold symEval at h
  split at h
  next hb =>
    apply symStats_sound C hC _ k w.a w.c n b s _ h
    unfold SymRep
    have hw : w.eval n=w.a*9^n+w.c := by unfold Aff.eval; rw [hb,Int.zero_mul,Int.add_zero]
    rw [hw] at hr
    omega
  next => contradiction

theorem dominance_abs {k : Aff} {W B : Int} (h : dominance k W B=true) (n : Nat) :
    -((3:Int)^(k.eval n).toNat) ≤ W*9^n+B ∧ W*9^n+B ≤ (3:Int)^(k.eval n).toNat := by
  obtain ⟨hk,hp⟩ := dominance_sound h n
  let l := (k.eval n-2*n).toNat
  have hle : (k.eval n).toNat=l+2*n := by dsimp [l]; omega
  have hq : 0≤(9:Int)^n := Int.le_of_lt (Int.pow_pos (by decide))
  have hq1 : 1≤(9:Int)^n := by have h:=pow9_lower n; omega
  have hB := Int.mul_le_mul_of_nonneg_left hq1 (show 0≤(B.natAbs:Int) by omega)
  simp only [Int.mul_one] at hB
  have hW1 := Int.mul_le_mul_of_nonneg_right (show -(W.natAbs:Int)≤W by omega) hq
  have hW2 := Int.mul_le_mul_of_nonneg_right (show W≤(W.natAbs:Int) by omega) hq
  have hp' : (W.natAbs+B.natAbs:Int)≤3^l := by dsimp [l]; omega
  have hh := Int.mul_le_mul_of_nonneg_right hp' hq
  rw [Int.add_mul] at hh
  rw [hle,Int.pow_add,←pow9_eq]
  rw [Int.neg_mul] at hW1
  omega

theorem powerGE_complete {k n : Nat} (h : n≤3^k) : powerGE k n=true := by
  unfold powerGE
  split
  · rfl
  · simp [h]

def domAff (k w : Aff) : Bool := decide (w.b=0) && dominance k w.a w.c

theorem domAff_abs {k w : Aff} (h : domAff k w=true) (n : Nat) :
    -((3:Int)^(k.eval n).toNat)≤w.eval n ∧ w.eval n≤(3:Int)^(k.eval n).toNat := by
  simp only [domAff,Bool.and_eq_true,decide_eq_true_eq] at h
  have hh := dominance_abs h.2 n
  unfold Aff.eval
  rw [h.1,Int.zero_mul,Int.add_zero]
  exact hh

theorem domAff_lower {C : Nat} {k w : Aff} (hc : 0<C) (h : domAff k w=true) (n : Nat) :
    lowerBound C (k.eval n).toNat (w.eval n) 0=true := by
  have habs := domAff_abs h n
  have hcast : ((3^((k.eval n).toNat):Nat):Int)=(3:Int)^((k.eval n).toNat) := Int.natCast_pow _ _
  unfold lowerBound
  simp only [hc,decide_true,Bool.true_and,Int.natCast_zero,Int.mul_zero,Int.zero_sub]
  apply powerGE_complete
  rw [←hcast] at habs
  omega

def modConst (f : Aff) (m : Int) : Int := (f.a+f.c)%m

def symParity (C : Nat) (k w : Aff) (p : Nat) : Bool :=
  ge k 0 && modEq k 2 (modConst k 2) && modEq w 4 (modConst w 4) &&
    parityOK C (k.eval 0).toNat (w.eval 0) p

theorem symParity_sound {C p : Nat} {k w : Aff} (h : symParity C k w p=true) (n : Nat) :
    parityOK C (k.eval n).toNat (w.eval n) p=true := by
  simp only [symParity,Bool.and_eq_true] at h
  have hk := ge_sound h.1.1.1 n
  have hk0 := ge_sound h.1.1.1 0
  have hmk := modEq_sound (Or.inl rfl) h.1.1.2 n
  have hmk0 := modEq_sound (Or.inl rfl) h.1.1.2 0
  have hmw := modEq_sound (Or.inr (Or.inl rfl)) h.1.2 n
  have hmw0 := modEq_sound (Or.inr (Or.inl rfl)) h.1.2 0
  have hnat : (k.eval n).toNat%2=(k.eval 0).toNat%2 := by omega
  have hpow : powMod4 (k.eval n).toNat=powMod4 (k.eval 0).toNat := by unfold powMod4; rw [hnat]
  have hw : w.eval n%4=w.eval 0%4 := by omega
  have hh : p<2 ∧ ((C:Int)*powMod4 (k.eval 0).toNat+w.eval 0)%4=2*(p:Int) := by simpa [parityOK] using h.2
  unfold parityOK
  apply decide_eq_true
  rw [hpow,Int.add_emod,hw,←Int.add_emod]
  exact hh

structure SymState where
  C : Nat
  D : Nat
  k : Aff
  u : Aff
  v : Aff
  deriving Repr, DecidableEq

def SymState.atN (s : SymState) (n : Nat) : NearState := ⟨s.C,s.D,(s.k.eval n).toNat,s.u.eval n,s.v.eval n⟩

def symGuard (s : SymState) : Bool :=
  decide (0<s.C ∧ 0<s.D) && ge s.k (8+(s.D+1).log2+1) &&
    domAff (s.k-ac 1) s.u && domAff (s.k-ac 1) s.v

private theorem exp8 (k : Nat) (hk : 5≤k) : 8*k≤3^(k-1) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h : 5≤k
    · have hh := ih h
      rw [show k+1-1=k by omega,show k=k-1+1 by omega,Nat.pow_succ]
      omega
    · have he : k=4 := by omega
      subst k; decide

private theorem exp32 (k : Nat) : 3^k≤2^(2*k) := by
  induction k with
  | zero => decide
  | succ k ih => rw [Nat.pow_succ,show 2*(k+1)=2*k+2 by omega,Nat.pow_add]; omega

theorem symGuard_sound {s : SymState} {n x y : Nat} (h : symGuard s=true) (hr : Represents (s.atN n) x y) :
    0<(s.atN n).k ∧ 0<s.C ∧ 0<s.D ∧ 2*(y.log2+1)≤x ∧ 14<y := by
  simp only [symGuard,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨hC,hD⟩ := h.1.1.1
  have hk := ge_sound h.1.1.2 n
  let k := (s.k.eval n).toNat
  let L := (s.D+1).log2+1
  have hkL : 8+L≤k := by dsimp [k,L]; omega
  have hku : ((s.k-ac 1).eval n).toNat=k-1 := by simp [k]
  have hu := domAff_abs h.1.2 n
  have hv := domAff_abs h.2 n
  rw [hku] at hu hv
  have he : (3:Int)^k=3*(3:Int)^(k-1) := by conv => lhs; rw [show k=k-1+1 by omega,Int.pow_succ,Int.mul_comm]
  have hp : 0≤(3:Int)^(k-1) := Int.le_of_lt (Int.pow_pos (by decide))
  have hmC := Int.mul_le_mul_of_nonneg_right (show (1:Int)≤s.C by omega) (show 0≤(3:Int)^k by exact Int.le_of_lt (Int.pow_pos (by decide)))
  have hmD := Int.mul_le_mul_of_nonneg_right (show (1:Int)≤s.D by omega) (show 0≤(3:Int)^k by exact Int.le_of_lt (Int.pow_pos (by decide)))
  simp only [Int.one_mul] at hmC hmD
  have hx := hr.1; have hy := hr.2
  change 2*(x:Int)=(s.C:Int)*3^k+s.u.eval n at hx
  change 2*(y:Int)=(s.D:Int)*3^k+s.v.eval n at hy
  have hxlo : (3:Int)^(k-1)≤x := by omega
  have hylo : (3:Int)^(k-1)≤y := by omega
  have hyhi : (y:Int)≤((s.D:Int)+1)*3^k := by
    rw [Int.add_mul,Int.one_mul]
    omega
  have h8 := exp8 k (by omega)
  have hcast : ((3^(k-1):Nat):Int)=(3:Int)^(k-1) := Int.natCast_pow _ _
  rw [←hcast] at hxlo hylo
  have hDpow : s.D+1<2^L := (Nat.log2_lt (by omega : s.D+1≠0)).mp (by dsimp [L]; omega)
  have h3 := exp32 k
  have hmul := Nat.mul_lt_mul_of_lt_of_le hDpow h3 (show 0<2^(2*k) by exact Nat.pow_pos (by decide))
  rw [←Nat.pow_add] at hmul
  have hyhiNat : y≤(s.D+1)*3^k := by
    have hh : (((s.D+1)*3^k:Nat):Int)=((s.D:Int)+1)*3^k := by simp only [Int.natCast_mul,Int.natCast_add,Int.natCast_one,Int.natCast_pow]; rfl
    rw [←hh] at hyhi; omega
  have hyl : y.log2<L+2*k := (Nat.log2_lt (by omega : y≠0)).mpr (by omega)
  exact ⟨by change 0<k; omega,hC,hD,by omega,by omega⟩

#print axioms symEval_sound
#print axioms symParity_sound
#print axioms symGuard_sound
end BB6.Agent41NearPower
