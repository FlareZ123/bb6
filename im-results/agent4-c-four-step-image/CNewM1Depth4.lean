import CNewM1
import Lean.Elab.Tactic.Omega

namespace BB6.Agent4Four
open BB6.Agent46

/-- A second disjoint infinite m=1 high-stopping class from the fourth
    affine lift, at j=266 modulo 256. -/
theorem high_one_j266_stopping (q : Nat) :
    (15*(256*q+266)+40)+(256*q+266)+3*1+5 =
      (2:Nat)^(2*1+2)*((256*q+266)+3) := by
  simp only [show (2:Nat)^(2*1+2)=16 by decide]
  omega

theorem high_one_j266_blank_unreachable (q time : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (2*(256*q+266)+3,15*(256*q+266)+40) := by
  have hx : 2*(256*q+266)+3=8*(64*q+64)+7+4*4 := by omega
  have hy : 15*(256*q+266)+40=bandY 4 (15*q+13) := by
    simp only [bandY, show (2:Nat)^4=16 by decide]
    omega
  simpa only [hx,hy] using
    blank_excludes_all_depth_cylinders 4 (64*q+64) (15*q+13) time

/-- Both infinite excluded m=1 families have j residue ten modulo sixteen,
    yet their j residue classes modulo 64 are disjoint. -/
theorem m1_two_classes_disjoint (a b : Nat) :
    64*a+26 ≠ 256*b+266 := by omega

theorem high_one_j266_passes_agent19_dyadic (q n : Nat) :
    ¬(n+4≤2*1+2 ∧
      ((256*q+266)+3*1+3)%2^(n+4)=2^(n+2) ∧
      (2*(256*q+266)+3)%8=(if n%2=0 then 7 else 3)) := by
  intro h
  have hn : n=0 := by omega
  subst n
  simp only [show (2:Nat)^(0+4)=16 by decide,
    show (2:Nat)^(0+2)=4 by decide] at h
  omega

#print axioms high_one_j266_stopping
#print axioms high_one_j266_blank_unreachable
#print axioms m1_two_classes_disjoint
#print axioms high_one_j266_passes_agent19_dyadic
end BB6.Agent4Four
