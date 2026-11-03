module
public import SecondGateway
@[expose] public section
namespace BB6.Agent16OddPower

private theorem exp5_aux (k : Nat) : 5*(k+6)+17 < 2^(k+6) := by
  induction k with
  | zero => decide
  | succ k ih =>
      have hp : 64≤2^(k+6) := by
        have h := Nat.pow_le_pow_right (by decide : 0<2) (show 6≤k+6 by omega)
        simpa using h
      have hs : 2^((k+1)+6)=2*2^(k+6) := by
        rw [show (k+1)+6=(k+6)+1 by omega,Nat.pow_succ]
        omega
      rw [hs]
      omega

private theorem exp5_gap (a : Nat) (ha : 6≤a) :
  5*a+17 < 2^a := by
  have hr : a=(a-6)+6 := by omega
  have he := exp5_aux (a-6)
  rw [←hr] at he
  exact he

private theorem power_no_gap (b m n : Nat)
    (hlo : 2^m < b) (hhi : b < 2^(m+1)) : 2^n ≠ b := by
  intro he
  by_cases hn : n≤m
  · have hp : 2^n≤2^m := Nat.pow_le_pow_right (by decide) hn
    omega
  · have hp : 2^(m+1)≤2^n := Nat.pow_le_pow_right (by decide) (by omega)
    omega

/-- No exceptional u=3 source returns to any positive odd-power gateway. -/
theorem no_special_second_gate (a k : Nat) (ha : 1≤a) :
   3*2^a+a+3 ≠ 2*gateOdd k := by
  intro he
  have hgate : 5*gateOdd k+1=2^(4*k+4) := gateOdd_equation k
  have hnext : 2^(4*k+5)=2*2^(4*k+4) := by
    rw [show 4*k+5=(4*k+4)+1 by omega,Nat.pow_succ]
    omega
  have ht : 2^(4*k+5)=15*2^a+5*a+17 := by omega
  by_cases halarge : 6≤a
  · have hgap := exp5_gap a halarge
    have h3 : 2^(a+3)=8*2^a := by
      rw [Nat.pow_add]
      change 2^a*8=8*2^a
      omega
    have h4 : 2^(a+4)=16*2^a := by
      rw [Nat.pow_add]
      change 2^a*16=16*2^a
      omega
    have hlo : 2^(a+3)<15*2^a+5*a+17 := by rw [h3]; omega
    have hhi : 15*2^a+5*a+17 < 2^(a+4) := by rw [h4]; omega
    exact power_no_gap _ (a+3) (4*k+5) hlo hhi ht
  · have cases : a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 := by omega
    rcases cases with h|h|h|h|h
    · subst a
      have hb : 2^(4*k+5)=52 := by simpa using ht
      exact power_no_gap 52 5 (4*k+5) (by decide) (by decide) hb
    · subst a
      have hb : 2^(4*k+5)=87 := by simpa using ht
      exact power_no_gap 87 6 (4*k+5) (by decide) (by decide) hb
    · subst a
      have hb : 2^(4*k+5)=152 := by simpa using ht
      exact power_no_gap 152 7 (4*k+5) (by decide) (by decide) hb
    · subst a
      have hb : 2^(4*k+5)=277 := by simpa using ht
      exact power_no_gap 277 8 (4*k+5) (by decide) (by decide) hb
    · subst a
      have hb : 2^(4*k+5)=522 := by simpa using ht
      exact power_no_gap 522 9 (4*k+5) (by decide) (by decide) hb

/-- Every section source of the odd-power gateway has a valuation a∈{1,...,5}. -/
theorem second_parent_valuation_small {s k : Nat}
  (hs : SectionStep s (2*gateOdd k)) :
  ∃ a v, 1≤a ∧ a≤5 ∧ 5≤v ∧ v%2=1 ∧ s=2^a*v ∧
    2^a*v+a+(v-1)/2=2*gateOdd k := by
  generalize hvalue : 2*gateOdd k = y at hs
  cases hs with
  | special a ha =>
    exact False.elim (no_special_second_gate a k ha hvalue.symm)
  | generic a v ha hv ho =>
    have ha_le : a≤5 := by
      by_cases hla : a≤5
      · exact hla
      · exact False.elim (no_large_generic_second_gate a v k (by omega) hv ho hvalue.symm)
    exact ⟨a,v,ha,ha_le,hv,ho,rfl,rfl⟩

#print axioms no_special_second_gate
#print axioms second_parent_valuation_small
end BB6.Agent16OddPower
