import Agent49TernaryShiftSource
import Agent8BudgetSource

/-! Original-source authenticated research on the #623 affine buffer.
DeepMind Cryptids source SHA c86f15861709b76042998c5211c7b2f83991621b.
Every theorem is about the source highLevelNext, not a blank-root decision.
-/
namespace BB6.Agent49TernaryBufferSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent49TernaryShiftSource
private abbrev next : HighLevelState → Option HighLevelState := highLevelNext

/-- Sharp universal source evaluator potential. -/
theorem evalA_first3 (a : Nat) : ∀ k m aa bb dd : Nat,
    evalA a k m = some (aa,bb,dd) → 3*aa+bb ≤ 3*a+k+1 := by
  induction a with
  | zero =>
    intro k m aa bb dd h
    rw [evalA] at h
    by_cases h2 : k%3=2
    · simp [h2] at h
      cases h
      omega
    · by_cases h0 : k%3=0
      · simp [h2,h0] at h
      · simp [h2,h0] at h
        cases h
        omega
  | succ a ih =>
    intro k m aa bb dd h
    rw [evalA] at h
    by_cases h2 : k%3=2
    · simp [h2] at h
      cases h
      omega
    · by_cases h0 : k%3=0
      · simp [h2,h0] at h
        cases h
        omega
      · simp [h2,h0] at h
        have hh:=ih (k/3) (m+2*(k/3)+3) aa bb dd h
        omega

/-- Universal B-drain bound: 3*output_first≤3*input_first+input_index. -/
theorem drainB_first3 (b : Nat) : ∀ a d aa dd : Nat,
    drainB a b d = some (.D aa dd) → 3*aa ≤ 3*a+b := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a d aa dd h
    rw [drainB] at h
    by_cases hb : b=0
    · simp [hb] at h
      cases h
      omega
    · simp only [if_neg hb] at h
      cases he : evalA a (b-1) (d+2*b+3) with
      | none => simp [he] at h
      | some p =>
        rcases p with ⟨a1,b1,d1⟩
        simp only [he,Option.bind_some] at h
        by_cases hlt : b1<b
        · simp only [if_pos hlt] at h
          have hp := evalA_first3 a (b-1) (d+2*b+3) a1 b1 d1 he
          have hr := ih b1 hlt a1 d1 aa dd h
          omega
        · simp [hlt] at h

#print axioms evalA_first3
#print axioms drainB_first3

/-- A successful near-left odd-d return from even a lies in the
old strongly safe right cone whenever it is outside the old left cone. -/
theorem far_left_odd_to_safe_right (a d b e : Nat)
    (ha : a%2=0) (hd : d%2=1) (hleft : d+5≤a)
    (hnotold : a≤2*d+8) (hnext : next (.D a d)=some (.D b e)) :
    b%2=0 ∧ 2*b+2≤e := by
  have hfirst : drainB (a-d-5) (d+3) 5=some (.D b e) := by
    have hz : a≠0 := by omega
    have hbranch : d%2=1 ∧ a≥d+5 := ⟨hd,hleft⟩
    simpa only [next,highLevelNext,if_neg hz,if_pos hbranch] using hnext
  have hf:=drainB_first3 (d+3) (a-d-5) 5 b e hfirst
  have hg:=BB6.Agent8BudgetSource.drainB_d3 (d+3) (a-d-5) 5 b e hfirst
  have hp:=BB6.Agent49ParitySource.drainB_parity (d+3) (a-d-5) 5 b e hfirst
  constructor <;> omega

/-- Even-d near-left branch has the same strong-right conclusion. -/
theorem far_left_even_to_safe_right (a d b e : Nat)
    (ha : a%2=0) (hd : d%2=0) (hleft : d+3≤a)
    (hnotold : a≤2*d+4) (hnext : next (.D a d)=some (.D b e)) :
    b%2=0 ∧ 2*b+2≤e := by
  have hfirst : drainB (a-d-2) (d+2) 2=some (.D b e) := by
    have hz : a≠0 := by omega
    have hno : ¬(d%2=1 ∧ a≥d+5) := by omega
    have hyes : d%2=0 ∧ a≥d+3 := ⟨hd,hleft⟩
    simpa only [next,highLevelNext,if_neg hz,if_neg hno,if_pos hyes] using hnext
  have hf:=drainB_first3 (d+2) (a-d-2) 2 b e hfirst
  have hg:=BB6.Agent8BudgetSource.drainB_d3 (d+2) (a-d-2) 2 b e hfirst
  have hp:=BB6.Agent49ParitySource.drainB_parity (d+2) (a-d-2) 2 b e hfirst
  constructor <;> omega

#print axioms far_left_odd_to_safe_right
#print axioms far_left_even_to_safe_right


/-- Near-right odd-d returns land in old strong-right sector once a≥22. -/
theorem right_odd_to_safe_right_large (a d b e : Nat)
    (ha : a%2=0) (ha0:0<a) (hd : d%2=1) (hside : a≤d)
    (hnotold : d<2*a+1) (hbig : 22≤a)
    (hnext : next (.D a d)=some (.D b e)) :
    b%2=0 ∧ 2*b+2≤e := by
  have hfirst : drainB (d+4-a) (a-1) 3=some (.D b e) := by
    have h0 : a≠0 := by omega
    have h1 : ¬(d%2=1 ∧ a≥d+5) := by omega
    have h2 : ¬(d%2=0 ∧ a≥d+3) := by omega
    have hodd : a%2≠1 := by omega
    have hdiff : a≠d+2 := by omega
    simp only [next,highLevelNext,if_neg h0,if_neg h1,if_neg h2,if_neg hodd,
      if_neg hdiff,if_pos hd] at hnext
    exact hnext
  have hf:=drainB_first3 (a-1) (d+4-a) 3 b e hfirst
  have hg:=BB6.Agent8BudgetSource.drainB_d3 (a-1) (d+4-a) 3 b e hfirst
  have hp:=BB6.Agent49ParitySource.drainB_parity (a-1) (d+4-a) 3 b e hfirst
  constructor <;> omega

/-- Near-right even-d return bound, using evaluator and drain budgets. -/
theorem right_even_to_safe_right_large (a d b e : Nat)
    (ha : a%2=0) (ha0:0<a) (hd : d%2=0) (hside : a≤d)
    (hnotold : d<2*a+2) (hbig : 6≤a)
    (hnext : next (.D a d)=some (.D b e)) :
    b%2=0 ∧ 2*b+2≤e := by
  have hrun : (evalA (d+1-a) a (2*a+5)).bind
        (fun p => drainB p.1 p.2.1 p.2.2) =some (.D b e) := by
    have h0 : a≠0 := by omega
    have h1 : ¬(d%2=1 ∧ a≥d+5) := by omega
    have h2 : ¬(d%2=0 ∧ a≥d+3) := by omega
    have hodd : a%2≠1 := by omega
    have hdiff : a≠d+2 := by omega
    have hdodd : d%2≠1 := by omega
    simpa only [next,highLevelNext,if_neg h0,if_neg h1,if_neg h2,if_neg hodd,
      if_neg hdiff,if_neg hdodd] using hnext
  cases heval : evalA (d+1-a) a (2*a+5) with
  | none => simp [heval] at hrun
  | some p =>
    rcases p with ⟨a1,b1,d1⟩
    simp only [heval,Option.bind_some] at hrun
    have hf:=evalA_first3 (d+1-a) a (2*a+5) a1 b1 d1 heval
    have ht:=BB6.Agent8BudgetSource.evalA_ternary_budget (d+1-a) a (2*a+5) a1 b1 d1 heval
    have hp:=BB6.Agent49ParitySource.evalA_parity (d+1-a) a (2*a+5) a1 b1 d1 heval
    have hb:=drainB_first3 b1 a1 d1 b e hrun
    have hg:=BB6.Agent8BudgetSource.drainB_d3 b1 a1 d1 b e hrun
    have hc:=BB6.Agent49ParitySource.drainB_parity b1 a1 d1 b e hrun
    constructor <;> omega

#print axioms right_odd_to_safe_right_large
#print axioms right_even_to_safe_right_large

end BB6.Agent49TernaryBufferSource
