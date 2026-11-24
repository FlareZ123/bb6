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

/-- Uniform source-level exclusion from any proved Boolean-prefix obstruction. -/
theorem source_wall_no_prefix (n b d m z k : Nat) (hn : 14 ≤ n)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hkn : k+1 ≤ n) (hkm : k+1 ≤ m)
    (hno : ¬ ∃ rest : List Bool, rest.length = k ∧
      BB6WallCarry.bitExpr n rest % 2^(k+1)=1) :
    b+4*m+4*n+20 ≠ 12*2^n := by
  intro hw
  obtain ⟨A,hnd,_,hstart,hId⟩ := source_wall_cost_list_identity n b d m z hn h hw
  rw [weight_eq] at hId
  obtain ⟨rest,hlen,hbits⟩ := BB6WallBridge.wall_identity_implies_bits
    n m k (costPowSum A) A hnd (hstart (by omega)) hkn hkm hId
  rw [bitExpr_eq] at hbits
  exact hno ⟨rest,hlen,hbits⟩

theorem source_no_wall_familyI_h1 (n b d m z u t : Nat)
    (hN : n=5362+595056*(1+2^56*t))
    (hU : 1058*u+636=17*2^n) (hM : m=14*u-2*n-3)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z) :
    b+4*m+4*n+20 ≠ 12*2^n := by
  have hn : 14≤n := by omega
  have hmN : n≤m := by
    rw [hM]
    exact BB6WallCarry.familyI_terminal_m_ge_n n u hn hU
  apply source_wall_no_prefix n b d m z 59 hn h (by omega) (by omega)
  rw [hN]
  exact BB6WallCarry.noPrefix_familyI_h1 t

theorem source_no_wall_familyI_h2 (n b d m z u t : Nat)
    (hN : n=5362+595056*(2+2^8*t))
    (hU : 1058*u+636=17*2^n) (hM : m=14*u-2*n-3)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z) :
    b+4*m+4*n+20 ≠ 12*2^n := by
  have hn : 14≤n := by omega
  have hmN : n≤m := by
    rw [hM]
    exact BB6WallCarry.familyI_terminal_m_ge_n n u hn hU
  apply source_wall_no_prefix n b d m z 11 hn h (by omega) (by omega)
  rw [hN]
  exact BB6WallCarry.noPrefix_familyI_h2 t

theorem source_no_wall_familyII_h1 (n b d m z u t : Nat)
    (hN : n=9538+703248*(1+2^10*t))
    (hU : 1198*u+712=87*2^n) (hM : m=14*u-2*n-3)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z) :
    b+4*m+4*n+20 ≠ 12*2^n := by
  have hn : 14≤n := by omega
  have hmN : n≤m := by
    rw [hM]
    exact BB6WallCarry.familyII_terminal_m_ge_n n u hn hU
  apply source_wall_no_prefix n b d m z 13 hn h (by omega) (by omega)
  rw [hN]
  exact BB6WallCarry.noPrefix_familyII_h1 t

theorem source_no_wall_familyII_h2 (n b d m z u t : Nat)
    (hN : n=9538+703248*(2+2^18*t))
    (hU : 1198*u+712=87*2^n) (hM : m=14*u-2*n-3)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z) :
    b+4*m+4*n+20 ≠ 12*2^n := by
  have hn : 14≤n := by omega
  have hmN : n≤m := by
    rw [hM]
    exact BB6WallCarry.familyII_terminal_m_ge_n n u hn hU
  apply source_wall_no_prefix n b d m z 21 hn h (by omega) (by omega)
  rw [hN]
  exact BB6WallCarry.noPrefix_familyII_h2 t

#print axioms source_cost_witness
#print axioms source_wall_cost_list_identity
#print axioms source_wall_no_prefix
#print axioms source_no_wall_familyI_h1
#print axioms source_no_wall_familyI_h2
#print axioms source_no_wall_familyII_h1
#print axioms source_no_wall_familyII_h2
end BB6.Agent43WallListSource
