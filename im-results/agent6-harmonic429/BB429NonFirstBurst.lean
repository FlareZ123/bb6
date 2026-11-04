import BB429Rank
import BB429Burst
import BB429PowerBarrierBurst
import Lean.Elab.Tactic.Omega

namespace BB429NonFirstBurst

/-- Every non-first successful macro transition entering a positive first
    counter has second counter 2 modulo 4. -/
set_option maxHeartbeats 5000000 in
theorem nonfirst_positive_modfour (x y u w : Nat)
    (hnot : y < 2*x+3)
    (hs : BB429.next (x,y) = some (u,w))
    (hpos : 0 < u) : w%4=2 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

/-- At the end of any first-only burst following a positive non-first
    return, the burst count modulo 4 is determined by the seed first
    counter's parity. -/
theorem positive_nonfirst_burst_length (x y u w n a b : Nat)
    (hnot : y < 2*x+3)
    (hs : BB429.next (x,y) = some (u,w))
    (hpos : 0 < u)
    (hr : BB429Burst.firstRun n (u,w) = some (a,b))
    (hg : b+1=2*a) :
    (u%2=1 ∧ n%4=1) ∨ (u%2=0 ∧ n%4=3) := by
  have hm := nonfirst_positive_modfour x y u w hnot hs hpos
  have he := (BB429Burst.gateway_iff_exponential u w n a b hr).mp hg
  omega

/-- The complete three-case endpoint classification: an immediate single
    first step from odd u, a three-step first burst from even u, or a
    longer burst landing at u=29 mod32. -/
theorem positive_nonfirst_burst_shape (x y u w n a b : Nat)
    (hnot : y < 2*x+3)
    (hs : BB429.next (x,y) = some (u,w))
    (hpos : 0 < u)
    (hr : BB429Burst.firstRun n (u,w) = some (a,b))
    (hg : b+1=2*a) :
    (n=1 ∧ u%2=1 ∧ a=2*u+3) ∨
    (n=3 ∧ u%2=0 ∧ a=8*u+21) ∨
    (5 ≤ n ∧ a%32=29) := by
  have hc := positive_nonfirst_burst_length x y u w n a b hnot hs hpos hr hg
  by_cases hshort : n < 5
  · rcases hc with ⟨hodd, hlen⟩ | ⟨heven, hlen⟩
    · have h1 : n=1 := by omega
      subst n
      have he := (BB429Burst.prefix_formula u w 1 a b hr).1
      simp at he
      left
      constructor
      · rfl
      constructor
      · exact hodd
      · omega
    · have h3 : n=3 := by omega
      subst n
      have he := (BB429Burst.prefix_formula u w 3 a b hr).1
      norm_num at he
      right
      left
      constructor
      · rfl
      constructor
      · exact heven
      · omega
  · right
    right
    have hl : 5 ≤ n := by omega
    exact ⟨hl, BB429PowerBarrierBurst.first_run_long_mod32 u w n a b hr hl⟩

#print axioms nonfirst_positive_modfour
#print axioms positive_nonfirst_burst_length
#print axioms positive_nonfirst_burst_shape
end BB429NonFirstBurst
