import BB429Branch29
import BB429FiniteAvoidance
import Lean.Elab.Tactic.Omega

/-!
# A deep inverse restriction on the remaining 29 mod 32 odd-reset class

The family q mod16 = 7 is ruled out uniformly for every q>=21,
except potentially the *single* exceptional integer q=55.
At that index the intermediate parent counter equals 11, which has
additional high-branch preimages; they are not silently omitted.
This is an all-time rooted nonreachability theorem, not a halt decision.
-/

namespace BB429Branch29Mod16
open BB429Reset31
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000

/-- For odd successor first counter a>=3 other than 11, there are
exactly the two ordinary source-inverse branches. Unlike the older
lemma requiring a>=13, this works also for a=3,5,7,9. -/
theorem odd_inverse_except_eleven (x y a b : Nat)
    (ha : 3≤a) (ho : a%2=1) (hne : a≠11)
    (hs : BB429.next (x,y)=some (a,b)) :
    (a=2*x+3 ∧ y=b+a) ∨
    (4*x+26=4*a+b ∧ 2*y=b+4 ∧ b%4=2) := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

/-- For q=16r+7, r>=1 and r!=3, the first seven exact ancestors
of the odd-reset family force an impossible even/odd root section.
The sole r=3 case (q=55) is excluded from this statement because
the target a=11 has additional source parents. -/
theorem no_29_q_seven_mod16_except55 (q : Nat)
    (hq : 21≤q) (hq16 : q%16=7) (h55 : q≠55) :
    ¬Reach (32*q+29) (64*q+55) := by
  intro hroot
  let r := q/16
  have hqeq : q=16*r+7 := by dsimp [r]; omega
  have hr : 1≤r := by omega
  have h3 := BB429Branch29.first_three q hroot
  have h5 := BB429Branch29.to_q_minus_two q hq h3
  obtain ⟨x6,y6,hp6,hx6,hy6⟩ :=
    BB429Branch29.odd_q_parent q hq (by omega) h5
  have hx6 : x6=8*r+1 := by omega
  have hy6 : y6=2032*r+989 := by omega
  rw [hx6,hy6] at hp6
  obtain ⟨x7,y7,hp7,hs7⟩ :=
    pred (8*r+1) (2032*r+989) (by omega) hp6
  obtain ⟨h7a,h7b⟩ :=
    BB429OddResetGate.incoming_odd_second x7 y7
      (8*r+1) (2032*r+989) hs7 (by omega)
  have hx7 : x7=4*r-1 := by omega
  have hy7 : y7=2040*r+990 := by omega
  rw [hx7,hy7] at hp7
  obtain ⟨x8,y8,hp8,hs8⟩ :=
    pred (4*r-1) (2040*r+990) (by omega) hp7
  rcases odd_inverse_except_eleven x8 y8
      (4*r-1) (2040*r+990) (by omega) (by omega) (by omega)
      hs8 with hF | hS
  · obtain ⟨h8a,h8b⟩ := hF
    have hx8 : x8=2*r-2 := by omega
    have hy8 : y8=2044*r+989 := by omega
    rw [hx8,hy8] at hp8
    obtain ⟨n,hn⟩ := hp8
    by_cases hone : r=1
    · have hallowed :=
        BB429Mod8.all_blank_returns_allowed n
          (2*r-2) (2044*r+989) hn
      unfold BB429Mod8.Allowed at hallowed
      omega
    · have he := BB429NoThree.reachable_even_positive n
        (2*r-2) (2044*r+989) hn (by omega) (by omega)
      omega
  · obtain ⟨h8a,h8b,h8mod⟩ := hS
    have hx8 : x8=514*r+240 := by omega
    have hy8 : y8=1020*r+497 := by omega
    rw [hx8,hy8] at hp8
    obtain ⟨n,hn⟩ := hp8
    have he := BB429NoThree.reachable_even_positive n
      (514*r+240) (1020*r+497) hn (by omega) (by omega)
    omega

/-- All-time necessary restriction on the authentic blank-root
odd-reset 29-mod-32 subfamily. Only q=2,10,15 mod16 or the isolated
unresolved q=55 are compatible with the exact inverse and known
rooted arithmetic invariants. -/
theorem rooted_29_q_three_mod16_or_55 (q : Nat)
    (hq : 21≤q)
    (hroot : Reach (32*q+29) (64*q+55)) :
    q%16=2 ∨ q%16=10 ∨ q%16=15 ∨ q=55 := by
  have h8 := BB429Branch29.rooted_29_q_two_of_eight q hq hroot
  by_cases h7 : q%16=7
  · by_cases h55 : q=55
    · exact Or.inr (Or.inr (Or.inr h55))
    · exact False.elim (no_29_q_seven_mod16_except55 q hq h7 h55 hroot)
  · omega


/-- The q=55 exception is impossible: forced true-blank ancestor (11,7110)
contradicts the finite prefix plus strict-rank certificate. -/
theorem no_29_q55 : ¬Reach (32*55+29) (64*55+55) := by
  intro hroot
  have h3 := BB429Branch29.first_three 55 hroot
  have h5 := BB429Branch29.to_q_minus_two 55 (by omega) h3
  obtain ⟨x6,y6,hp6,hx6,hy6⟩ :=
    BB429Branch29.odd_q_parent 55 (by omega) (by omega) h5
  have h6x : x6=25 := by omega
  have h6y : y6=7085 := by omega
  rw [h6x,h6y] at hp6
  obtain ⟨x7,y7,hp7,hs7⟩ :=
    pred 25 7085 (by omega) hp6
  obtain ⟨ha,hb⟩ :=
    BB429OddResetGate.incoming_odd_second x7 y7 25 7085
      hs7 (by omega)
  have h7x : x7=11 := by omega
  have h7y : y7=7110 := by omega
  rw [h7x,h7y] at hp7
  exact BB429FiniteAvoidance.no_root_11_7110 hp7

/-- Complete all-time rooted restriction for q>=21 with no exception:
only q=2,10,15 mod16 remain. -/
theorem rooted_29_q_three_mod16 (q : Nat) (hq : 21≤q)
    (hroot : Reach (32*q+29) (64*q+55)) :
    q%16=2 ∨ q%16=10 ∨ q%16=15 := by
  have h :=
    rooted_29_q_three_mod16_or_55 q hq hroot
  rcases h with h2 | h10 | h15 | h55
  · exact Or.inl h2
  · exact Or.inr (Or.inl h10)
  · exact Or.inr (Or.inr h15)
  · subst q
    exact False.elim (no_29_q55 hroot)

#print axioms no_29_q55
#print axioms rooted_29_q_three_mod16

#print axioms odd_inverse_except_eleven
#print axioms no_29_q_seven_mod16_except55
#print axioms rooted_29_q_three_mod16_or_55
end BB429Branch29Mod16
