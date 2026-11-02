import DeepCorridor

namespace BB6.P1Deep
open BB6.Agent1

/-- Indices n+2 = 2^(L+4) lie in the unresolved n≡14(mod16) sector. -/
def critIndex (L : Nat) : Nat := 2^(L+4)-2

def critWeight (L : Nat) : Nat :=
  7*2^(critIndex L-(L+4))-1

private theorem power_growth (L : Nat) : L+7 ≤ 2^(L+4) := by
  induction L with
  | zero => decide
  | succ L ih =>
    have hpow : (2:Nat)^((L+1)+4) = 2*(2^(L+4)) := by
      have he : (L+1)+4 = (L+4)+1 := by omega
      rw [he,Nat.pow_succ]
      omega
    rw [hpow]
    omega

theorem crit_index_add (L : Nat) : critIndex L + 2 = 2^(L+4) := by
  dsimp [critIndex]
  have hbound := power_growth L
  omega

theorem crit_index_ge (L : Nat) : L+4 ≤ critIndex L := by
  have hbound := power_growth L
  have hplus := crit_index_add L
  omega

theorem crit_weight_lower (L : Nat) : 3≤critWeight L := by
  have hp : 1 ≤ (2:Nat)^(critIndex L-(L+4)) :=
    Nat.one_le_pow _ 2 (by decide)
  dsimp [critWeight]
  omega

private theorem power_split (L : Nat) :
    2^(critIndex L) = 2^(L+4)*2^(critIndex L-(L+4)) := by
  have hge := crit_index_ge L
  have he : critIndex L = (L+4)+(critIndex L-(L+4)) := by omega
  calc
    2^(critIndex L) = 2^((L+4)+(critIndex L-(L+4))) :=
      congrArg (fun e : Nat => 2^e) he
    _ = 2^(L+4)*2^(critIndex L-(L+4)) := by rw [Nat.pow_add]

/-- The corridor root is exactly the genuine P1 critical-index G hub. -/
theorem critical_root_eq (L : Nat) :
    left (L+2) (critWeight L) 0 =
      14*2^(critIndex L)-2*(critIndex L)-16 := by
  let Q : Nat := 2^(L+5)
  let P : Nat := 2^(critIndex L-(L+4))
  let K : Nat := critWeight L
  have hpow := power_split L
  have hplus := crit_index_add L
  have hweight : K+1=7*P := by
    dsimp [K,critWeight,P]
    have hp : 1 ≤ (2:Nat)^(critIndex L-(L+4)) :=
      Nat.one_le_pow _ 2 (by decide)
    omega
  have hQ : Q=2*2^(L+4) := by
    dsimp [Q]
    rw [show L+5=(L+4)+1 by omega, Nat.pow_succ]
    omega
  have h14 : 14*2^(critIndex L)=Q*(K+1) := by
    rw [hpow,hQ,hweight]
    dsimp [P]
    change (2*7)*(2^(L+4)*2^(critIndex L-(L+4))) =
      (2*2^(L+4))*(7*2^(critIndex L-(L+4)))
    ac_rfl
  have h14' : 14*2^(critIndex L)=Q*K+Q := by
    rw [h14]
    simp [Nat.mul_add]
  have hsub : 2*(critIndex L)+16=Q+12 := by omega
  have hb : left (L+2) K 0=Q*K-12 := by
    dsimp [left,Q]
    have hpowe : 8*2^(L+2)=2^(L+5) := by
      have hpow2 : 2^(L+5)=2^(L+2)*2^3 := by
        rw [show L+5=(L+2)+3 by omega,Nat.pow_add]
      rw [hpow2]
      simp only [show (2:Nat)^3=8 by decide]
      ac_rfl
    rw [hpowe]
  rw [hb]
  omega

/-- Every L has a genuine critical P1 root with an L-long backward corridor.
    No blank-start reachability of its synthetic predecessors is claimed. -/
theorem critical_unbounded_predecessor_corridor (L : Nat) :
    let m := L+2
    let K := critWeight L
    let n := critIndex L
    3 ≤ K ∧
    left m K 0 = 14*2^n-2*n-16 ∧
    right m K 0 = 3 ∧
    (∀ i : Nat, i<L →
      T (left m K (i+1)) (right m K (i+1)) =
        some (left m K (i+1)+3,right m K (i+1)-2) ∧
      T (left m K (i+1)+3) (right m K (i+1)-2) =
        some (left m K i,right m K i)) := by
  dsimp
  refine ⟨crit_weight_lower L,critical_root_eq L,rfl,?_⟩
  intro i hi
  exact corridor_link (L+2) (critWeight L) i (crit_weight_lower L) (by omega)

#print axioms BB6.P1Deep.critical_root_eq
#print axioms BB6.P1Deep.critical_unbounded_predecessor_corridor
end BB6.P1Deep
