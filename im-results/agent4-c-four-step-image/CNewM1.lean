import CAllDepthBlank
import Lean.Elab.Tactic.Omega

namespace BB6.Agent4Four
open BB6.Agent46

/-- An infinite genuine m=1 high-stopping family, different from
    Agent 19's all-depth dyadic high filter: j=26 modulo 64. -/
theorem high_one_j26_stopping (q : Nat) :
    (15*(64*q+26)+40)+(64*q+26)+3*1+5 =
      (2:Nat)^(2*1+2)*((64*q+26)+3) := by
  simp only [show (2:Nat)^(2*1+2)=16 by decide]
  omega

/-- Every one of these m=1 high-stop inputs is absent from the authentic
    blank-origin Machine C first-return orbit at every natural time. -/
theorem high_one_j26_blank_unreachable (q time : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (2*(64*q+26)+3,15*(64*q+26)+40) := by
  have hx : 2*(64*q+26)+3=8*(16*q+5)+7+4*2 := by omega
  have hy : 15*(64*q+26)+40=bandY 2 (15*q+4) := by
    simp only [bandY, show (2:Nat)^2=4 by decide]
    omega
  simpa only [hx,hy] using
    blank_excludes_all_depth_cylinders 2 (16*q+5) (15*q+4) time

/-- The older Agent 19 all-depth high obstruction cannot use any
    valuation depth here: m=1 permits only n=0 and that residue fails. -/
theorem high_one_j26_passes_agent19_dyadic (q n : Nat) :
    ¬(n+4≤2*1+2 ∧
      ((64*q+26)+3*1+3)%2^(n+4)=2^(n+2) ∧
      (2*(64*q+26)+3)%8=(if n%2=0 then 7 else 3)) := by
  intro h
  have hn : n=0 := by omega
  subst n
  simp only [show (2:Nat)^(0+4)=16 by decide,
    show (2:Nat)^(0+2)=4 by decide] at h
  omega

#print axioms high_one_j26_stopping
#print axioms high_one_j26_blank_unreachable
#print axioms high_one_j26_passes_agent19_dyadic
end BB6.Agent4Four
