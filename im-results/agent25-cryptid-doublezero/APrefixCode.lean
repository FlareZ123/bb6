import DoubleZeroE
import TokenCode
namespace CryptidA
def eb (m : Nat) (ys : List Bool) : Cfg :=
  ⟨false :: false :: (pat m ++ [true,true]), false, ys, 4⟩
theorem a_zero (m : Nat) (ys : List Bool) :
    run (2*m+6) (ab m (false :: ys)) = finish (2*m+5) ys := by
  exact close_double_zero m ys
theorem a_ten (m : Nat) (ys : List Bool) :
    run 2 (ab m ([true,false] ++ ys)) = ab (m+1) ys := ten_pump m ys
theorem a_e_gate (m : Nat) (ys : List Bool) :
    run 3 (ab m ([true,true,false] ++ ys)) = eb (m+1) ys := by
  simp [run, step, goR, ab, eb, pat]
theorem a_triple (m : Nat) (ys : List Bool) :
    run (6*m+41) (ab m ([true,true,true] ++ ys)) = ab (m+4) ys := triplet_pump m ys
#print axioms a_e_gate
end CryptidA
