import BB429NewResidue
import BB429RootEven8
import BB429RootOddRows
import Lean.Elab.Tactic.Omega

namespace BB429LastResetOddRows
open BB429NewResidue

/-- An odd/odd reachable state with first counter 3 mod 4 has sum 2 mod 8.
The second inverse branch is impossible because its second counter is 2 mod 4. -/
theorem odd_odd_mod4_three_sum (a b : Nat)
    (hr : Reach a b) (ha : 13 ≤ a) (hao : a%2=1)
    (hbo : b%2=1) (ha4 : a%4=3) : (a+b)%8=2 := by
  rcases odd_back a b ha hao hr with hfirst | hsecond
  · rcases hfirst with ⟨x,y,hp,hax,hby⟩
    rcases hp with ⟨n,hn⟩
    have hxpos : 0 < x := by omega
    have hxeven : x%2=0 := by omega
    have h8 := BB429RootEven8.rooted_positive_even_eight n x y hn hxpos hxeven
    rw [hby] at h8
    omega
  · rcases hsecond with ⟨x,y,hp,hax,hby,hb4⟩
    omega

/-- All-time odd/odd row restrictions for the authentic blank-root orbit. -/
theorem rooted_odd_odd_rows (a b : Nat)
    (hr : Reach a b)
    (ha : 13≤a) (hao : a%2=1) (hbo : b%2=1) :
    (a%16=1 → b%8=1) ∧
    (a%16=3 → b%8=7) ∧
    (a%16=7 → b%8=3) ∧
    (a%16=9 → b%8=1 ∨ b%8=5) ∧
    (a%16=11 → b%8=7) ∧
    (a%16=15 → b%8=3) := by
  have hrCopy := hr
  rcases hrCopy with ⟨n,hn⟩
  have hall := reach_allowed a b hr
  constructor
  · intro ha1
    have hb4 : b%4=1 := by
      unfold BB429Mod8.Allowed at hall
      omega
    have hb8 : b%8=1 ∨ b%8=5 := by omega
    rcases hb8 with h | h
    · exact h
    · exact False.elim (Agent6RootOddRows.rooted_not_1_5 n a b hn ha1 h)
  · constructor
    · intro ha3
      have hsum := odd_odd_mod4_three_sum a b hr ha hao hbo (by omega)
      omega
    · constructor
      · intro ha7
        have hsum := odd_odd_mod4_three_sum a b hr ha hao hbo (by omega)
        omega
      · constructor
        · intro ha9
          have hb4 : b%4=1 := by
            unfold BB429Mod8.Allowed at hall
            omega
          omega
        · constructor
          · intro ha11
            have hsum := odd_odd_mod4_three_sum a b hr ha hao hbo (by omega)
            omega
          · intro ha15
            have hsum := odd_odd_mod4_three_sum a b hr ha hao hbo (by omega)
            omega

#print axioms odd_odd_mod4_three_sum
#print axioms rooted_odd_odd_rows

end BB429LastResetOddRows
