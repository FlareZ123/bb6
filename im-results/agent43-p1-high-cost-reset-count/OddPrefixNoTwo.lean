import Lean.Elab.Tactic.Omega
import RootTwoDivisor

namespace BB6.Agent43TwoRun

/-- For odd critical index n, a depth-two scalar prefix cannot even take
its first step: the root dyadic defect has exact valuation one modulo four. -/
theorem odd_index_no_initial_two
    (n s : Nat) (Wa Ba : Int)
    (hn : 14≤n) (hodd : n % 2 = 1)
    (hpre : TwoRun ((2:Int)^n)
      (14*(2:Int)^n+2*(n:Int)+4) ((n:Int)+6) s Wa Ba) :
    s=0 := by
  obtain ⟨h3s,hdvd⟩ := root_two_prefix_divisor n s Wa Ba hn hpre
  by_cases hs : s = 0
  · exact hs
  have hspos : 1≤s := by omega
  have hpow : 8 ∣ (8:Nat)^s := by
    obtain ⟨t,ht⟩ : ∃ t, s=t+1 := ⟨s-1, by omega⟩
    rw [ht, Nat.pow_succ]
    exact Nat.dvd_mul_left _ _
  have hdiv : 8 ∣ 14*n+92 := Nat.dvd_trans hpow hdvd
  obtain ⟨k,hk⟩ := hdiv
  omega

#print axioms BB6.Agent43TwoRun.odd_index_no_initial_two
end BB6.Agent43TwoRun