import EvenTargetForward
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- No even-middle original bounce ever returns a right counter of exactly 4.
    Proof exhausts all base cases and all arbitrarily deep recursive paths. -/
theorem bounce_even_no_four (K c x : Nat) (hK:K%2=0) :
    (bounce K c).2≠some (x,4) := by
  induction c using Nat.strongRecOn generalizing K x with
  | ind c ih =>
    intro hb
    by_cases hlow : c<4
    · simp [bounce,hlow] at hb
    · have hnotodd : K%2≠1 := by omega
      by_cases hc4 : c=4
      · simp [bounce,hlow,hnotodd,hc4] at hb
      · by_cases hc5 : c=5
        · simp [bounce,hlow,hnotodd,hc4,hc5] at hb
        · by_cases hs : c≤2*K+8
          · have hh:=hb
            rw [bounce] at hh
            simp only [if_neg hlow,if_neg hnotodd,if_neg hc4,if_neg hc5,if_pos hs] at hh
            have heq := Option.some.inj hh
            have hp := Prod.mk.inj heq
            omega
          · have hlt:c-(2*K+5)<c := by omega
            have hh : (bounce (2*K+4) (c-(2*K+5))).2=some (x,4) := by
              have hh:=hb
              rw [bounce] at hh
              simpa only [if_neg hlow,if_neg hnotodd,if_neg hc4,if_neg hc5,if_neg hs] using hh
            exact ih (c-(2*K+5)) hlt (2*K+4) x (by omega) hh

#print axioms bounce_even_no_four
end BB6.Agent46
