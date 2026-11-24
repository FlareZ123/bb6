import BitExact
import BitGroupCert
namespace BB6.Agent28ScalarTail
open BB6.Agent28BitCarry BB6.Agent28BitExact BB6.Agent28BitSpread BB6.Agent28BitGroup BB6.Agent45.DelayedCarry

theorem spreadStep_single (L k i : Nat) (hk : k<L) (hi : i<2^L) :
    spreadStep L k (2^(packedPos (k+1) i))=2^(packedPos k i) := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases he : p=packedPos k i
  · subst p
    rw [Nat.testBit_two_pow_self]
    exact spreadStep_sound L k _ i hk hi Nat.testBit_two_pow_self
  · rw [Nat.testBit_two_pow]
    have hf : decide (packedPos k i=p)=false := by simp [Ne.symm he]
    rw [hf]
    by_cases hb : (spreadStep L k (2^(packedPos (k+1) i))).testBit p=true
    · exfalso
      simp only [spreadStep,Nat.testBit_and,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_two_pow,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at hb
      have hgood := laneMask_support (2^k) (L-k) p (Nat.two_pow_pos _) hb.2
      have hlow : packedPos k i%(2*2^k)<2^k := by rw [packedPos_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
      have hflip := opposite_lane (2^k) (packedPos (k+1) i) (Nat.two_pow_pos _)
      rcases packedPos_step k i with hpos|hpos
      · rcases hb.1 with h1|⟨h1,h2⟩
        · omega
        · have hpeq : p=packedPos (k+1) i+2^k := by omega
          rw [hpeq] at hgood
          rw [hpos] at hlow
          have hh := hflip.mp hlow
          omega
      · rcases hb.1 with h1|⟨h1,h2⟩
        · rw [← h1] at hgood
          have hh := hflip.mp hgood
          rw [hpos] at hlow
          omega
        · omega
    · cases hh : (spreadStep L k (2^(packedPos (k+1) i))).testBit p <;> simp_all

theorem spreadFrom_single (L k i : Nat) (hk : k≤L) (hi : i<2^L) :
    spreadFrom L k (2^(packedPos k i))=2^(packedPos 0 i) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [spreadFrom,spreadStep_single L k i (by omega) hi,ih (by omega)]

theorem spreadEven_single (L i : Nat) (hi : i<2^L) : spreadEven L (2^i)=2^(2*i) := by
  have hpos0 : packedPos 0 i=2*i := by simp [packedPos]; omega
  have hposL : packedPos L i=i := by simp [packedPos,Nat.div_eq_of_lt hi,Nat.mod_eq_of_lt hi]
  have he := spreadFrom_single L L i (by omega) hi
  simpa [spreadEven,hpos0,hposL] using he

theorem reverseStep_single (L C y c : Nat) (hC : 0<C) (hc : c<2^L) (hh : 2*c+y<2*C) :
    reverseStep L C y (2^c)=2^((2*c+y)%C) := by
  unfold reverseStep
  rw [spreadEven_single L c hc,Nat.shiftLeft_eq,← Nat.pow_add]
  apply Nat.eq_of_testBit_eq
  intro p
  rw [Nat.testBit_and,Nat.testBit_or,Nat.testBit_shiftRight,Nat.testBit_two_pow_sub_one]
  simp only [Nat.testBit_two_pow]
  by_cases h : 2*c+y<C
  · rw [Nat.mod_eq_of_lt h]
    by_cases he : p=2*c+y
    · subst p; simp [h]
    · have h1 : 2*c+y≠p := by omega
      have h2 : 2*c+y≠C+p := by omega
      simp [h1,h2]
  · have hr : (2*c+y)%C=2*c+y-C := by
      rw [Nat.mod_eq_sub_mod (by omega)]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hr]
    by_cases he : p=2*c+y-C
    · subst p
      have h1 : 2*c+y=C+(2*c+y-C) := by omega
      have h2 : 2*c+y-C<C := by omega
      have h3 : decide (2*c+y=C+(2*c+y-C))=true := decide_eq_true h1
      rw [h3]
      simp [h2]
    · by_cases hl : p<C
      · have h1 : 2*c+y≠p := by omega
        have h2 : 2*c+y≠C+p := by omega
        have h3 : 2*c+y-C≠p := by omega
        simp [h1,h2,h3]
      · have h3 : 2*c+y-C≠p := by omega
        simp [hl,h3]

theorem reverseStep_single_zero (L C y c : Nat) (hC : 0<C) (hc : c<2^L) (hh : 2*C≤2*c+y) :
    reverseStep L C y (2^c)=0 := by
  unfold reverseStep
  rw [spreadEven_single L c hc,Nat.shiftLeft_eq,← Nat.pow_add]
  apply Nat.eq_of_testBit_eq
  intro p
  rw [Nat.testBit_and,Nat.testBit_or,Nat.testBit_shiftRight,Nat.testBit_two_pow_sub_one]
  simp only [Nat.testBit_two_pow,Nat.zero_testBit]
  by_cases h : p<C
  · have h1 : 2*c+y≠p := by omega
    have h2 : 2*c+y≠C+p := by omega
    simp [h1,h2]
  · simp [h]

def scalarBack (n B s : Nat) : Nat → Nat → Option Nat
  | 0,c => some c
  | k+1,c =>
    let C := n+s+k+3
    let u := 2*c+target n (s+k) B
    if u<2*C then scalarBack n B s k (u%C) else none

theorem spreadEven_zero (L : Nat) : spreadEven L 0=0 := by
  unfold spreadEven
  have h (k : Nat) : spreadFrom L k 0=0 := by
    induction k with
    | zero => rfl
    | succ k ih => simpa [spreadFrom,spreadStep] using ih
  exact h L

theorem backRun_zero (L n B s k : Nat) : backRun L n B s k 0=0 := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [backRun,reverseStep,spreadEven_zero] using ih

theorem backRun_scalar (L n B s k c : Nat) (hc : c<2^L)
    (hb : n+s+k+2<2^L) :
    backRun L n B s k (2^c)=(scalarBack n B s k c).elim 0 (fun d=>2^d) := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    let C := n+s+k+3
    let y := target n (s+k) B
    change backRun L n B s k (reverseStep L C y (2^c)) =
      (if 2*c+y<2*C then scalarBack n B s k ((2*c+y)%C) else none).elim 0 (fun d=>2^d)
    have hC : 0<C := by dsimp [C]; omega
    have hCb : C<2^L := by dsimp [C]; omega
    by_cases h : 2*c+y<2*C
    · rw [if_pos h,reverseStep_single L C y c hC hc h]
      exact ih _ (Nat.lt_trans (Nat.mod_lt _ hC) hCb) (by omega)
    · rw [if_neg h,reverseStep_single_zero L C y c hC hc (by omega),backRun_zero]
      rfl

theorem backRun_coalesce (L n B s k j bits c d : Nat)
    (hc : c<2^L) (hb : n+s+k+2<2^L)
    (h1 : backRun L n B (s+k) j bits=2^c)
    (h2 : scalarBack n B s k c=some d) :
    backRun L n B s (k+j) bits=2^d := by
  rw [backRun_add,h1,backRun_scalar L n B s k c hc hb,h2]
  rfl

#print axioms spreadEven_single
#print axioms reverseStep_single
#print axioms backRun_scalar
#print axioms backRun_coalesce
end BB6.Agent28ScalarTail
