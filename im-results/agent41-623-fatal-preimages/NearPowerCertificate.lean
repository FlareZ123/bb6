import NearPowerFastStats

/-! A compressed arithmetic certificate for one positive-budget inverse sector.
A strict bracket excludes the entire parity class; an equality specifies its
unique candidate. No large power is needed to check long near-power tails. -/
namespace BB6.Agent41NearPower
open BB6.Agent49CorrectionGrowth

def powerGE (k n : Nat) : Bool :=
  if n.log2+1≤k then true else decide (n≤3^k)

theorem powerGE_sound {k n : Nat} (h : powerGE k n = true) : n≤3^k := by
  unfold powerGE at h
  split at h
  next hlog =>
    by_cases hz : n=0
    · subst n; exact Nat.zero_le _
    · have hl := (Nat.log2_lt hz).mp (show n.log2<n.log2+1 by omega)
      have hp : 2^(n.log2+1)≤2^k := Nat.pow_le_pow_right (by decide) hlog
      have hp' : 2^k≤3^k := Nat.pow_le_pow_left (by decide) k
      omega
  next => simpa using h

def lowerBound (C k : Nat) (w : Int) (n : Nat) : Bool :=
  decide (0<C) && powerGE k (2*(n:Int)-w).toNat

theorem lowerBound_sound {C k n : Nat} {w : Int}
    (h : lowerBound C k w n=true) : 2*(n:Int)≤(C:Int)*3^k+w := by
  simp only [lowerBound,Bool.and_eq_true,decide_eq_true_eq] at h
  have hp := powerGE_sound h.2
  have he : ((3^k:Nat):Int)=(3:Int)^k := Int.natCast_pow 3 k
  have hpi : 2*(n:Int)-w≤(3:Int)^k := by rw [←he]; omega
  have hpos : (0:Int)<3^k := Int.pow_pos (by decide)
  have hm := Int.mul_le_mul_of_nonneg_right (show (1:Int)≤C by omega) (Int.le_of_lt hpos)
  simp only [Int.one_mul] at hm
  omega

def powMod4 (k : Nat) : Int := if k%2=0 then 1 else 3

theorem powMod4_correct (k : Nat) : (3:Int)^k%4=powMod4 k := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Int.pow_succ,Int.mul_emod,ih]
    unfold powMod4
    split <;> split <;> omega

def parityOK (C k : Nat) (w : Int) (p : Nat) : Bool :=
  decide (p<2 ∧ ((C:Int)*powMod4 k+w)%4=2*(p:Int))

theorem parityOK_sound {C k p : Nat} {w : Int}
    (h : parityOK C k w p=true) : ((C:Int)*3^k+w)%4=2*(p:Int) := by
  have hh : p<2 ∧ ((C:Int)*powMod4 k+w)%4=2*(p:Int) := by simpa [parityOK] using h
  rw [Int.add_emod,Int.mul_emod,powMod4_correct]
  rw [Int.add_emod,Int.mul_emod] at hh
  have hm : powMod4 k % 4=powMod4 k := by unfold powMod4; split <;> decide
  rw [hm] at hh
  exact hh.2

theorem blockRep_exists {C k p : Nat} {w : Int}
    (hlo : lowerBound C k w 0=true) (hp : parityOK C k w p=true) :
    ∃ b : Nat, 2*(b:Int)=(C:Int)*3^k+w ∧ b%2=p := by
  have hl := lowerBound_sound hlo
  have hm := parityOK_sound hp
  have hpar : p<2 := by simp [parityOK] at hp; exact hp.1
  refine ⟨blockVal C k w,?_,?_⟩ <;> unfold blockVal <;> omega

def imageResidual (C k z : Nat) (w : Int) : Int :=
  3*w+2*((fastStats C k w).2+z:Nat)

theorem imageResidual_correct {C k b z : Nat} {w : Int} (hC : 0<C)
    (h : 2*(b:Int)=(C:Int)*3^k+w) :
    2*((z+image b:Nat):Int)=(C:Int)*3^(k+1)+imageResidual C k z w := by
  have hs := fastStats_correct C k b w hC h
  unfold imageResidual image
  rw [hs,Int.pow_succ,←Int.mul_assoc,Int.mul_comm _ (3:Int)]
  simp only [Prod.snd,Int.natCast_add,Int.natCast_mul]
  omega

/-- The exact next block in the same parity class skips no other block. -/
theorem parity_gap {b c z y : Nat} (hp : b%2=c%2)
    (hlo : z+image b<y) (hhi : y<z+image (b+2)) : y≠z+image c := by
  intro he
  by_cases hc : c≤b
  · have hh : c+2*((b-c)/2)=b := by omega
    have hm := image_progression c ((b-c)/2)
    rw [hh] at hm
    omega
  · have hh : b+2+2*((c-(b+2))/2)=c := by omega
    have hm := image_progression (b+2) ((c-(b+2))/2)
    rw [hh] at hm
    omega

/-- A compressed strict bracket proves absence of every block of parity p. -/
def gapOK (C k z p : Nat) (w v : Int) : Bool :=
  lowerBound C k w 0 && parityOK C k w p &&
    decide (imageResidual C k z w<v ∧ v<imageResidual C k z (w+4))

theorem gapOK_sound {C k z p y : Nat} {w v : Int}
    (hy : 2*(y:Int)=(C:Int)*3^(k+1)+v)
    (h : gapOK C k z p w v=true) :
    ∀ c : Nat, c%2=p → y≠z+image c := by
  simp only [gapOK,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨b,hb,hp⟩ := blockRep_exists h.1.1 h.1.2
  have hC : 0<C := by simp [lowerBound] at h; exact h.1.1.1
  have hb' : 2*((b+2:Nat):Int)=(C:Int)*3^k+(w+4) := by omega
  have h0 := imageResidual_correct (z:=z) hC hb
  have h1 := imageResidual_correct (z:=z) hC hb'
  intro c hc
  exact parity_gap (by omega : b%2=c%2) (by omega) (by omega)

/-- Equality fixes the unique inverse block, without enumeration. -/
def hitOK (C k z p : Nat) (w v : Int) : Bool :=
  lowerBound C k w 0 && parityOK C k w p && decide (imageResidual C k z w=v)

theorem hitOK_sound {C k z p y : Nat} {w v : Int}
    (hy : 2*(y:Int)=(C:Int)*3^(k+1)+v)
    (h : hitOK C k z p w v=true) :
    ∃ b : Nat, 2*(b:Int)=(C:Int)*3^k+w ∧ b%2=p ∧ y=z+image b ∧
      ∀ c : Nat, y=z+image c → c=b := by
  simp only [hitOK,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨b,hb,hp⟩ := blockRep_exists h.1.1 h.1.2
  have hC : 0<C := by simp [lowerBound] at h; exact h.1.1.1
  have hi := imageResidual_correct (z:=z) hC hb
  refine ⟨b,hb,hp,by omega,?_⟩
  intro c hc
  exact image_injective (by omega)

#print axioms gapOK_sound
#print axioms hitOK_sound
end BB6.Agent41NearPower
