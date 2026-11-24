import DrainCorrectionGrowth

namespace BB6.Agent41NearPower
open BB6.Agent49CorrectionGrowth

def nextBlock (b : Nat) : Nat := b/3+b%3-1

def residue (w : Int) : Int := (2*w)%3

def residualStep (w : Int) : Int := (w+4*residue w-6)/3

def driftCharge (r : Nat) : Int := if r=0 then 1 else -1

def excessCharge (r : Nat) : Nat := if r=0 then 0 else if r=1 then 4 else 2

theorem nextBlock_stats (b : Nat) (hb : 0<b) :
    drift b=drift (nextBlock b)+driftCharge (b%3) ∧
    excess b=excess (nextBlock b)+excessCharge (b%3) := by
  have hr : b%3=0 ∨ b%3=1 ∨ b%3=2 := by omega
  rcases hr with hr|hr|hr
  · have hq : 0<b/3 := by omega
    have hrep : b=3*(b/3) := by omega
    have hnb : nextBlock b=b/3-1 := by simp [nextBlock,hr]
    rw [hnb]
    simp [driftCharge,excessCharge,hr]
    constructor
    · conv => lhs; rw [drift]
      simp [show b≠0 by omega,hr]
      omega
    · conv => lhs; rw [hrep,excess_three _ hq]
  · have hrep : b=3*(b/3)+1 := by omega
    have hnb : nextBlock b=b/3 := by simp [nextBlock,hr]
    rw [hnb]
    simp [driftCharge,excessCharge,hr]
    constructor
    · conv => lhs; rw [drift]
      simp [show b≠0 by omega,hr]
      omega
    · conv => lhs; rw [hrep,excess_one]
      omega
  · have hrep : b=3*(b/3)+2 := by omega
    have hnb : nextBlock b=b/3+1 := by simp [nextBlock,hr]
    rw [hnb]
    simp [driftCharge,excessCharge,hr]
    constructor
    · conv => lhs; rw [drift]
      simp [show b≠0 by omega,hr]
      omega
    · conv => lhs; rw [hrep,excess_two]
      omega

/-- Strip one low ternary digit, retaining the coefficient of the long
    near-power tail and updating only the signed residual. -/
theorem residual_step (C k b : Nat) (w : Int) (hb : 0<b)
    (h : 2*(b:Int)=(C:Int)*3^(k+1)+w) :
    ((b%3 : Nat):Int)=residue w ∧
    2*(nextBlock b:Int)=(C:Int)*3^k+residualStep w := by
  have he : (C:Int)*3^(k+1)=3*((C:Int)*3^k) := by
    rw [Int.pow_succ,← Int.mul_assoc,Int.mul_comm _ (3:Int)]
  rw [he] at h
  have hr : ((b%3 : Nat):Int)=residue w := by
    unfold residue
    omega
  constructor
  · exact hr
  · unfold residualStep
    rw [←hr]
    have hpos : 1≤b/3+b%3 := by omega
    have hn : (nextBlock b:Int)=(b/3:Nat)+(b%3:Nat)-1 := by
      unfold nextBlock; omega
    rw [hn]
    omega

/-- Three fixed residuals and one two-cycle. -/
theorem fixed_residuals : residualStep (-3) = -3 ∧
    residualStep (-1) = -1 ∧ residualStep 1 = 1 ∧
    residualStep (-2) = 0 ∧ residualStep 0 = -2 := by decide

theorem residual_contract (w : Int) :
    3* (residualStep w).natAbs ≤ w.natAbs+6 := by
  have hr0 : 0≤residue w := by unfold residue; omega
  have hr1 : residue w≤2 := by unfold residue; omega
  have hd : 3*residualStep w=w+4*residue w-6 := by
    unfold residualStep residue
    omega
  omega

/-- Any residual outside the bounded interval strictly contracts. -/
theorem residual_strict (w : Int) (h : 3<w.natAbs) :
    (residualStep w).natAbs<w.natAbs := by
  have h' := residual_contract w
  omega

/-- The two extra bounded residuals enter the fixed/cycle set in one step. -/
theorem residual_small (w : Int) (hw : w.natAbs≤3) :
    residualStep w=-3 ∨ residualStep w=-2 ∨ residualStep w=-1 ∨
    residualStep w=0 ∨ residualStep w=1 := by
  have hc : w=-3 ∨ w=-2 ∨ w=-1 ∨ w=0 ∨ w=1 ∨ w=2 ∨ w=3 := by omega
  rcases hc with h|h|h|h|h|h|h <;> subst w <;> decide

private theorem tail_pos (C k b : Nat) (w : Int) (hC : 0<C)
    (hw : -3≤w) (h : 2*(b:Int)=(C:Int)*3^(k+2)+w) : 0<b := by
  have hpow : (9:Int)≤3^(k+2) := by
    have ht : (1:Int)≤3^k := by
      have hp : (0:Int)<3^k := Int.pow_pos (by decide : (0:Int)<3)
      omega
    rw [show k+2=k+1+1 by omega,Int.pow_succ,Int.pow_succ]
    omega
  have hmul : (3:Int)^(k+2)≤(C:Int)*3^(k+2) := by
    have hh := Int.mul_le_mul_of_nonneg_right (show (1:Int)≤C by omega) (show 0≤(3:Int)^(k+2) by omega)
    simpa using hh
  omega

/-- Fixed-tail jump: k low steps can be replaced by a single linear update. -/
theorem fixed_tail (C k b c : Nat) (w : Int) (hC : 0<C)
    (hw : -3≤w) (hf : residualStep w=w)
    (hb : 2*(b:Int)=(C:Int)*3^(k+2)+w)
    (hc : 2*(c:Int)=(C:Int)*3^2+w) :
    drift b=drift c+(k:Int)*driftCharge (residue w).toNat ∧
    excess b=excess c+k*excessCharge (residue w).toNat := by
  induction k generalizing b with
  | zero =>
    have he : b=c := by omega
    subst b
    simp
  | succ k ih =>
    have hp := tail_pos C (k+1) b w hC hw hb
    have hbe : 2*(b:Int)=(C:Int)*3^((k+2)+1)+w := by
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb
    obtain ⟨hr,hn⟩ := residual_step C (k+2) b w hp hbe
    rw [hf] at hn
    have hnext := ih (nextBlock b) hn
    have hst := nextBlock_stats b hp
    have hmod : b%3=(residue w).toNat := by omega
    rw [hmod] at hst
    constructor
    · rw [hst.1,hnext.1,Int.natCast_succ,Int.add_mul]; omega
    · rw [hst.2,hnext.2,Nat.succ_mul]; omega

/-- Each full two-cycle contributes zero drift and two units of excess. -/
theorem cycle_tail (C k b c : Nat) (w : Int) (hC : 0<C)
    (hw : w=-2 ∨ w=0)
    (hb : 2*(b:Int)=(C:Int)*3^(2*k+2)+w)
    (hc : 2*(c:Int)=(C:Int)*3^2+w) :
    drift b=drift c ∧ excess b=excess c+2*k := by
  induction k generalizing b with
  | zero =>
    have he : b=c := by omega
    subst b
    simp
  | succ k ih =>
    have hp := tail_pos C (2*(k+1)) b w hC (by omega) hb
    have he : 2*(b:Int)=(C:Int)*3^((2*k+3)+1)+w := by
      simpa only [show 2*(k+1)+2=2*k+3+1 by omega] using hb
    obtain ⟨hr,hn⟩ := residual_step C (2*k+3) b w hp he
    have hw' : residualStep w=-2 ∨ residualStep w=0 := by
      rcases hw with h|h <;> subst w <;> decide
    have hn' : 2*(nextBlock b:Int)=(C:Int)*3^((2*k+1)+2)+residualStep w := by
      simpa only [show 2*k+1+2=2*k+3 by omega] using hn
    have hp' := tail_pos C (2*k+1) (nextBlock b) (residualStep w) hC (by omega) hn'
    have he' : 2*(nextBlock b:Int)=(C:Int)*3^((2*k+2)+1)+residualStep w := by
      simpa only [show 2*k+2+1=2*k+3 by omega] using hn
    obtain ⟨hr',hn''⟩ := residual_step C (2*k+2) (nextBlock b) (residualStep w) hp' he'
    have hf : residualStep (residualStep w)=w := by
      rcases hw with h|h <;> subst w <;> decide
    rw [hf] at hn''
    have hrest := ih (nextBlock (nextBlock b)) hn''
    have hst := nextBlock_stats b hp
    have hst' := nextBlock_stats (nextBlock b) hp'
    rcases hw with h|h
    · subst w
      have h1 : residue (-2)=2 := by decide
      have h2 : residue (residualStep (-2))=0 := by decide
      rw [h1] at hr
      rw [h2] at hr'
      have hm : b%3=2 := by omega
      have hm' : nextBlock b%3=0 := by omega
      rw [hm] at hst
      rw [hm'] at hst'
      simp [driftCharge,excessCharge] at hst hst'
      omega
    · subst w
      have h1 : residue 0=0 := by decide
      have h2 : residue (residualStep 0)=2 := by decide
      rw [h1] at hr
      rw [h2] at hr'
      have hm : b%3=0 := by omega
      have hm' : nextBlock b%3=2 := by omega
      rw [hm] at hst
      rw [hm'] at hst'
      simp [driftCharge,excessCharge] at hst hst'
      omega

#print axioms nextBlock_stats
#print axioms residual_step
#print axioms fixed_residuals
#print axioms residual_contract
#print axioms fixed_tail
#print axioms cycle_tail
end BB6.Agent41NearPower
