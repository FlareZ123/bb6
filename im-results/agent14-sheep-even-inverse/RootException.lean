import ExceptionThresholds
namespace SheepEvenBound
/-- The root 138 family cannot have exceptional odd-part-3 predecessors with h=0. -/
theorem root_h0_special (n a : Nat) (hn : 6 ≤ n) :
    2^n ≠ 3*2^a+a+3 := by
  have hb := exceptional_0_0 n hn
  by_cases ha : a ≤ n-2
  · have hp : 2^a ≤ 2^(n-2) := Nat.pow_le_pow_right (by decide) ha
    have hnexp : n=2+(n-2) := by omega
    have hp2 : 2^n=4*2^(n-2) := by
      have hp3 : 2^2=4 := by decide
      calc
        2^n = 2^(2+(n-2)) := congrArg (fun x => 2^x) hnexp
        _ = 4*2^(n-2) := by rw [Nat.pow_add]
    intro heq
    rw [hp2] at heq
    omega
  · have ha' : n-1 ≤ a := by omega
    have hp : 2^(n-1) ≤ 2^a := Nat.pow_le_pow_right (by decide) ha'
    have hnexp : n=1+(n-1) := by omega
    have hp2 : 2^n=2*2^(n-1) := by
      calc
        2^n = 2^(1+(n-1)) := congrArg (fun x => 2^x) hnexp
        _ = 2*2^(n-1) := by rw [Nat.pow_add]
    intro heq
    rw [hp2] at heq
    omega
#print axioms root_h0_special
end SheepEvenBound
