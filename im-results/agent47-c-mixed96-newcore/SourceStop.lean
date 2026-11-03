import SourceC
import SourceD
import GateArithmetic

set_option maxHeartbeats 0
namespace NewCore

theorem source_no_second_C5 (j m k : Nat)
    (hj : j%48=1) (hm : (j+3*m)%96=4)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬BB6CLine.Reach (2*j+3,k,0) := by
  intro h
  obtain ⟨ha,hk⟩ := second_C5 j m k hj hm heq
  exact source_no_cylinder_5_55 (2*j+3) k ha hk h

theorem source_no_second_C53 (j m k : Nat)
    (hj : j%48=25) (hm : (j+3*m)%96=52)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬BB6CLine.Reach (2*j+3,k,0) := by
  intro h
  obtain ⟨ha,hk⟩ := second_C53 j m k hj hm heq
  exact source_no_cylinder_53_7 (2*j+3) k ha hk h

theorem source_no_second_D37 (j m k : Nat)
    (hj : j%48=17) (hm : (j+3*m)%96=68)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬BB6CLine.Reach (2*j+3,k,0) := by
  intro h
  obtain ⟨ha,hk⟩ := second_D37 j m k hj hm heq
  exact source_no_cylinder_37_55 (2*j+3) k ha hk h

theorem source_no_second_D85 (j m k : Nat)
    (hj : j%48=41) (hm : (j+3*m)%96=20)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬BB6CLine.Reach (2*j+3,k,0) := by
  intro h
  obtain ⟨ha,hk⟩ := second_D85 j m k hj hm heq
  exact source_no_cylinder_85_7 (2*j+3) k ha hk h

theorem source_no_four_new_second (j m k : Nat)
    (hsector :
      (j%48=1 ∧ (j+3*m)%96=4) ∨
      (j%48=25 ∧ (j+3*m)%96=52) ∨
      (j%48=17 ∧ (j+3*m)%96=68) ∨
      (j%48=41 ∧ (j+3*m)%96=20))
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬BB6CLine.Reach (2*j+3,k,0) := by
  rcases hsector with ⟨hj,hm⟩ | ⟨hj,hm⟩ | ⟨hj,hm⟩ | ⟨hj,hm⟩
  · exact source_no_second_C5 j m k hj hm heq
  · exact source_no_second_C53 j m k hj hm heq
  · exact source_no_second_D37 j m k hj hm heq
  · exact source_no_second_D85 j m k hj hm heq

#print axioms source_no_four_new_second
end NewCore
