import SSourceBranch
import Init.Omega
namespace BB6.Agent9STransfer
open BB6.Agent9SExp BB6.Agent9SSourceBranch

/-- The published high-level S branch with its T-transfer counter retained. -/
def sourceSResult (b c : Nat) : Sum (Nat × Nat) Nat :=
  let a := 2*(b/3)
  if b % 3 = 0 then .inl (2*a+1,c+4)
  else if b % 3 = 1 then .inl (2*a+5,c+6)
  else if c=0 then .inr (2*a+7)
  else .inl (2*a+8,c-1)

/-- Exact T-transfer criterion and target in original b coordinates. -/
theorem transfer_iff (b c m : Nat) :
    sourceSResult b c = .inr m ↔
    b%3=2 ∧ c=0 ∧ m=4*(b/3)+7 := by
  unfold sourceSResult
  by_cases h0 : b%3=0
  · simp [h0]
  · by_cases h1 : b%3=1
    · simp [h0,h1]
    · by_cases hc : c=0
      · simp [h0,h1,hc]
        constructor
        · intro h
          omega
        · intro h
          rcases h with ⟨hr,_,hm⟩
          omega
      · simp [h0,h1,hc]

/-- The T transfer counter equals the q-only mathematical continuation
minus 17: m+17=f(b+16). -/
theorem transfer_q (b c m : Nat)
    (h : sourceSResult b c = .inr m) :
    c=0 ∧ (b+16)%3=0 ∧ m+17=nextQ (b+16) := by
  obtain ⟨hr,hc,hm⟩ := (transfer_iff b c m).mp h
  constructor
  · exact hc
  constructor
  · omega
  · unfold nextQ
    have hs : (b+16)%3=0 := by omega
    simp only [hs, if_true]
    omega

/-- Original S-only partial step agrees with the full source's S/T tag. -/
theorem sourceStep_iff_S (b c b' c' : Nat) :
    sourceSResult b c = .inl (b',c') ↔
    sourceStep (b,c) = some (b',c') := by
  unfold sourceSResult sourceStep
  by_cases h0 : b%3=0
  · simp [h0]
  · by_cases h1 : b%3=1
    · simp [h0,h1]
    · by_cases hc : c=0
      · simp [h0,h1,hc]
      · simp [h0,h1,hc]

theorem sourceStep_none_iff_transfer (b c : Nat) :
    sourceStep (b,c) = none ↔
    ∃ m, sourceSResult b c = .inr m := by
  unfold sourceStep sourceSResult
  by_cases h0 : b%3=0
  · simp [h0]
  · by_cases h1 : b%3=1
    · simp [h0,h1]
    · by_cases hc : c=0
      · simp [h0,h1,hc]
      · simp [h0,h1,hc]

#print axioms BB6.Agent9STransfer.transfer_q
#print axioms BB6.Agent9STransfer.sourceStep_none_iff_transfer
end BB6.Agent9STransfer
