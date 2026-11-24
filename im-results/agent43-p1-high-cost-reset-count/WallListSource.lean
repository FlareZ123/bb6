import CountedWallStrongGateSource
import WallListCore
import WallPrefixListBridge
import wall_prefix_carry_cylinders

namespace BB6.Agent43WallListSource

open BB6.Agent28 BB6.Agent1Quarter BB6.Agent1UpperTail BB6.Agent47P1
open BB6.Agent43LastResetStrength
open BB6.Agent43WallListCore

/-- Lift the locally checked list induction to every original CountCone edge. -/
theorem source_cost_witness (n b d m z : Nat) (hn : 14 ≤ n)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z) : CostWitness n d m := by
  induction h with
  | root => exact witness_root n
  | parent bp dp mp zp t k c hp hb hb4 hd hi hk hc ih =>
      have hodd : OddCone (14*2^n-2*n-16) 3 bp dp mp :=
        counted_to_odd_cone _ _ _ _ _ _ hp
      have hmass0 := odd_cone_mass _ _ bp dp mp hodd
      have hroot : (14*2^n-2*n-16)+3+2*n+13=14*2^n := by omega
      have hmass : bp+dp+2*mp+2*n+13=14*2^n := by omega
      have hpower := (inverseAt_iff_power_mass bp dp t k c
        (by omega) hb4 hd).mp hi
      have hpower2 : 2*(dp+bp/2+3)=2^(t+1)*(c+3) := by
        calc
          _ = 2*(2^t*(c+3)) := by rw [hpower.1]
          _ = _ := by rw [Nat.pow_succ]; ac_rfl
      have hrec : (dp-1)+14*2^n=2^(t+1)*((c+4)-1)+2*(mp+n+3) := by
        have hcd : (c+4)-1=c+3 := by omega
        rw [hcd, ← hpower2]
        omega
      simpa only [Nat.add_assoc] using
        witness_step n dp mp (t+1) (c+4) (by omega) ih hrec

theorem source_wall_cost_list_identity (n b d m z : Nat) (hn : 14 ≤ n)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hw : b+4*m+4*n+20=12*2^n) :
    ∃ A : List Nat, A.Nodup ∧ (∀ s ∈ A, s < m) ∧
      (0 < m → 0 ∈ A) ∧
      1+7*2^n*costPowSum A =
        2^n*2^m+costWeightedSum n A+(n+3+m)*2^m := by
  have hodd : OddCone (14*2^n-2*n-16) 3 b d m :=
    counted_to_odd_cone _ _ _ _ _ _ h
  have hmass0 := odd_cone_mass _ _ b d m hodd
  have hroot : (14*2^n-2*n-16)+3+2*n+13=14*2^n := by omega
  exact wall_from_witness n d m (source_cost_witness n b d m z hn h) (by omega)

private theorem weight_eq (n : Nat) (A : List Nat) :
    costWeightedSum n A = BB6WallBridge.costWeightedSum n A := by
  induction A with
  | nil => rfl
  | cons s A ih =>
    simp only [costWeightedSum, BB6WallBridge.costWeightedSum, BB6WallBridge.weight, ih]

private theorem sumBits_eq (n j : Nat) (A : List Bool) :
    BB6WallBridge.sumBits n j A = BB6WallCarry.sumBits n j A := by
  induction A generalizing j with
  | nil => rfl
  | cons b A ih =>
    simp only [BB6WallBridge.sumBits, BB6WallCarry.sumBits, ih]

private theorem bitExpr_eq (n : Nat) (A : List Bool) :
    BB6WallBridge.bitExpr n A = BB6WallCarry.bitExpr n A := by
  simp only [BB6WallBridge.bitExpr, BB6WallCarry.bitExpr, sumBits_eq]

/-- Every original critical-root history ends with an odd right counter. -/
theorem source_odd_right (n b d m z : Nat)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z) : d%2=1 := by
  induction h with
  | root => decide
  | parent bp dp mp zp t k c hp hb hb4 hd hi hk hc ih => omega

/-- No wall hypothesis is needed: an empty Boolean prefix layer bounds the
    total cost of EVERY genuine critical-root inverse history. -/
theorem source_countcone_cost_lt (n b d m z k : Nat) (hn : 14 ≤ n)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hkn : k+1 ≤ n)
    (hno : ¬ ∃ rest : List Bool, rest.length = k ∧
      BB6WallCarry.bitExpr n rest % 2^(k+1)=1) : m<k+1 := by
  by_cases hlt : m < k+1
  · exact hlt
  · exfalso
    have hkm : k+1≤m := by omega
    obtain ⟨A,hnd,h0,hmod⟩ := witness_mod_prefix n d m (k+1)
      (source_cost_witness n b d m z hn h) (source_odd_right n b d m z h)
      (by omega) hkn hkm
    rw [weight_eq] at hmod
    obtain ⟨rest,hlen,hbits⟩ := BB6WallBridge.weighted_mod_bits n k A hnd h0
    rw [bitExpr_eq] at hbits
    exact hno ⟨rest,hlen,hbits.symm.trans hmod⟩

theorem source_no_restart_familyI_h1 (n b d m z u t : Nat)
    (hN : n=5362+595056*(1+2^56*t))
    (hU : 1058*u+636=17*2^n) (hM : 14*u-2*n-3≤m) :
    ¬ CountCone (14*2^n-2*n-16) 3 b d m z := by
  intro h
  have hn : 14≤n := by omega
  have hmN : n≤m := Nat.le_trans
    (BB6WallCarry.familyI_terminal_m_ge_n n u hn hU) hM
  have hcap := source_countcone_cost_lt n b d m z 59 hn h (by omega) (by
    rw [hN]
    exact BB6WallCarry.noPrefix_familyI_h1 t)
  omega

theorem source_no_restart_familyI_h2 (n b d m z u t : Nat)
    (hN : n=5362+595056*(2+2^8*t))
    (hU : 1058*u+636=17*2^n) (hM : 14*u-2*n-3≤m) :
    ¬ CountCone (14*2^n-2*n-16) 3 b d m z := by
  intro h
  have hn : 14≤n := by omega
  have hmN : n≤m := Nat.le_trans
    (BB6WallCarry.familyI_terminal_m_ge_n n u hn hU) hM
  have hcap := source_countcone_cost_lt n b d m z 11 hn h (by omega) (by
    rw [hN]
    exact BB6WallCarry.noPrefix_familyI_h2 t)
  omega

theorem source_no_restart_familyII_h1 (n b d m z u t : Nat)
    (hN : n=9538+703248*(1+2^10*t))
    (hU : 1198*u+712=87*2^n) (hM : 14*u-2*n-3≤m) :
    ¬ CountCone (14*2^n-2*n-16) 3 b d m z := by
  intro h
  have hn : 14≤n := by omega
  have hmN : n≤m := Nat.le_trans
    (BB6WallCarry.familyII_terminal_m_ge_n n u hn hU) hM
  have hcap := source_countcone_cost_lt n b d m z 13 hn h (by omega) (by
    rw [hN]
    exact BB6WallCarry.noPrefix_familyII_h1 t)
  omega

theorem source_no_restart_familyII_h2 (n b d m z u t : Nat)
    (hN : n=9538+703248*(2+2^18*t))
    (hU : 1198*u+712=87*2^n) (hM : 14*u-2*n-3≤m) :
    ¬ CountCone (14*2^n-2*n-16) 3 b d m z := by
  intro h
  have hn : 14≤n := by omega
  have hmN : n≤m := Nat.le_trans
    (BB6WallCarry.familyII_terminal_m_ge_n n u hn hU) hM
  have hcap := source_countcone_cost_lt n b d m z 21 hn h (by omega) (by
    rw [hN]
    exact BB6WallCarry.noPrefix_familyII_h2 t)
  omega

theorem source_cost_zero_right_three (n b d m z : Nat)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z) (hm : m=0) : d=3 := by
  cases h with
  | root => rfl
  | parent bp dp mp zp t k c hp hb hb4 hd hi hk hc => omega

theorem source_small_cost_right (n b d m z : Nat) (hn : 14≤n)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z) (hm : m≤n)
    (hmpos : 0<m) : 15≤d :=
  witness_small_cost_right n d m (source_cost_witness n b d m z hn h)
    hn (BB6WallCarry.pow2_ge_1100_mul n hn) hm hmpos (source_odd_right n b d m z h)

/-- This closes the entire critical right-five gate for every index n with
    any impossible carry prefix of length K≤n, over all inverse depths. -/
theorem source_no_right_five_of_no_prefix (n b m z k : Nat) (hn : 14≤n)
    (hkn : k+1≤n)
    (hno : ¬ ∃ rest : List Bool, rest.length = k ∧
      BB6WallCarry.bitExpr n rest % 2^(k+1)=1) :
    ¬ CountCone (14*2^n-2*n-16) 3 b 5 m z := by
  intro h
  have hcap := source_countcone_cost_lt n b 5 m z k hn h hkn hno
  have hmpos : 0<m := by
    by_cases hm : m=0
    · have heq := source_cost_zero_right_three n b 5 m z h hm
      omega
    · omega
  have hright := source_small_cost_right n b 5 m z hn h (by omega) hmpos
  omega

/-- A short carry obstruction excluding all positive histories at odd indices. -/
theorem noPrefix_odd (n : Nat) (hn : n%2=1) :
    ¬ ∃ rest : List Bool, rest.length = 0 ∧ BB6WallCarry.bitExpr n rest % 2^1=1 := by
  rintro ⟨rest,hlen,hmod⟩
  have heq : rest=[] := List.length_eq_zero_iff.mp hlen
  subst rest
  simp [BB6WallCarry.bitExpr, BB6WallCarry.sumBits] at hmod
  omega

theorem noPrefix_mod16 (n : Nat) (heven : n%2=0)
    (h2 : n%16≠2) (h14 : n%16≠14) :
    ¬ ∃ rest : List Bool, rest.length = 3 ∧ BB6WallCarry.bitExpr n rest % 2^4=1 := by
  let r := n%16
  have hrEven : r%2=0 := by dsimp [r]; omega
  have hrCases : r=0 ∨ r=4 ∨ r=6 ∨ r=8 ∨ r=10 ∨ r=12 := by
    dsimp [r] at *
    omega
  have hempty : BB6WallCarry.carryStatesFrom r 1 [((r+2)/2)] 3 = [] := by
    rcases hrCases with h | h | h | h | h | h <;> rw [h] <;> decide
  have h := BB6WallCarry.noBitSubset_of_add_multiple r 3 (n/16) hrEven hempty
  have heq : r+2^(3+1)*(n/16)=n := by dsimp [r]; omega
  rw [heq] at h
  exact h

/-- Unlike the previous wall-only mod-16 criterion, this covers all right-five
    critical histories, including the high-cost non-wall branch. -/
theorem source_right_five_forces_mod16 (n b m z : Nat) (hn : 14≤n)
    (h : CountCone (14*2^n-2*n-16) 3 b 5 m z) :
    n%16=2 ∨ n%16=14 := by
  by_cases h2 : n%16=2
  · exact Or.inl h2
  · by_cases h14 : n%16=14
    · exact Or.inr h14
    · exfalso
      by_cases heven : n%2=0
      · exact source_no_right_five_of_no_prefix n b m z 3 hn (by omega)
          (noPrefix_mod16 n heven h2 h14) h
      · exact source_no_right_five_of_no_prefix n b m z 0 hn (by omega)
          (noPrefix_odd n (by omega)) h

theorem source_no_right_five_familyI_h1 (n b m z t : Nat)
    (hN : n=5362+595056*(1+2^56*t)) :
    ¬ CountCone (14*2^n-2*n-16) 3 b 5 m z := by
  have hn : 14≤n := by omega
  exact source_no_right_five_of_no_prefix n b m z 59 hn (by omega) (by
    rw [hN]
    exact BB6WallCarry.noPrefix_familyI_h1 t)

theorem source_no_right_five_familyI_h2 (n b m z t : Nat)
    (hN : n=5362+595056*(2+2^8*t)) :
    ¬ CountCone (14*2^n-2*n-16) 3 b 5 m z := by
  have hn : 14≤n := by omega
  exact source_no_right_five_of_no_prefix n b m z 11 hn (by omega) (by
    rw [hN]
    exact BB6WallCarry.noPrefix_familyI_h2 t)

theorem source_no_right_five_familyII_h1 (n b m z t : Nat)
    (hN : n=9538+703248*(1+2^10*t)) :
    ¬ CountCone (14*2^n-2*n-16) 3 b 5 m z := by
  have hn : 14≤n := by omega
  exact source_no_right_five_of_no_prefix n b m z 13 hn (by omega) (by
    rw [hN]
    exact BB6WallCarry.noPrefix_familyII_h1 t)

theorem source_no_right_five_familyII_h2 (n b m z t : Nat)
    (hN : n=9538+703248*(2+2^18*t)) :
    ¬ CountCone (14*2^n-2*n-16) 3 b 5 m z := by
  have hn : 14≤n := by omega
  exact source_no_right_five_of_no_prefix n b m z 21 hn (by omega) (by
    rw [hN]
    exact BB6WallCarry.noPrefix_familyII_h2 t)

#print axioms source_small_cost_right
#print axioms source_no_right_five_of_no_prefix
#print axioms source_right_five_forces_mod16
#print axioms source_no_right_five_familyI_h1
#print axioms source_no_right_five_familyI_h2
#print axioms source_no_right_five_familyII_h1
#print axioms source_no_right_five_familyII_h2

#print axioms source_cost_witness
#print axioms source_wall_cost_list_identity
#print axioms source_odd_right
#print axioms source_countcone_cost_lt
#print axioms source_no_restart_familyI_h1
#print axioms source_no_restart_familyI_h2
#print axioms source_no_restart_familyII_h1
#print axioms source_no_restart_familyII_h2
end BB6.Agent43WallListSource
