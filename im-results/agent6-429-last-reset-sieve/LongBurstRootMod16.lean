import BB429NewResidue
import BB429RootMod16
import Lean.Elab.Tactic.Omega

namespace BB429LastResetRootMod16

open BB429NewResidue

/-- The four branch-9 long-burst residue classes listed below force the
    forbidden rooted pair (7 mod 8, 7 mod 8). The obstruction is the
    existing kernel-proved BB429RootMod16.rooted_not_7_7 theorem. -/
theorem branch9_bad_d_classes_unreachable (n d x y : Nat)
    (hn : 18 ≤ n)
    (hcase :
      (n%32=1 ∧ d%16=12) ∨
      (n%32=9 ∧ d%16=8) ∨
      (n%32=17 ∧ d%16=4) ∨
      (n%32=25 ∧ d%16=0))
    (hdx : d ≤ x)
    (hx : 4*x + 3*n + 25 = 2^(n+2)*(d+10)+2*d)
    (hy : y = 2*(x-d)+1)
    (hr : Reach x y) : False := by
  have hexp : n+2 = 5+(n-3) := by omega
  have hpow : 2^(n+2) = 32 * 2^(n-3) := by
    rw [hexp, Nat.pow_add, show (2:Nat)^5 = 32 by decide]
  let t := 2^(n-3)*(d+10)
  have hx' : 4*x + 3*n + 25 = 32*t + 2*d := by
    dsimp [t]
    calc
      4*x + 3*n + 25 = 2^(n+2)*(d+10)+2*d := hx
      _ = (32*2^(n-3))*(d+10)+2*d := by rw [hpow]
      _ = 32*(2^(n-3)*(d+10))+2*d := by simp [Nat.mul_assoc]
  rcases hr with ⟨i,hi⟩
  have h77 := BB429RootMod16.rooted_not_7_7 i x y hi
  rcases hcase with ⟨hnc,hdc⟩ | ⟨hnc,hdc⟩ |
      ⟨hnc,hdc⟩ | ⟨hnc,hdc⟩
  all_goals
    have hx7 : x%8=7 := by omega
    have hy7 : y%8=7 := by omega
    exact h77 hx7 hy7

/-- Branch 8 of the last-reset table has y=1 and d=x even. It is already
    incompatible with the root mod-8 allowed-pair invariant. -/
theorem branch8_unreachable (x y : Nat)
    (hx : x%2=0)
    (hy : y=1)
    (hr : Reach x y) : False := by
  have ha := BB429NewResidue.reach_allowed x y hr
  unfold BB429Mod8.Allowed at ha
  omega

#print axioms branch9_bad_d_classes_unreachable
#print axioms branch8_unreachable

end BB429LastResetRootMod16
