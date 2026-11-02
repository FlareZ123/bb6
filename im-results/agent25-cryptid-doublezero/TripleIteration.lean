import TripleUniversal

namespace CryptidA

def tblock : Nat → List Bool
  | 0 => []
  | q + 1 => [true,true,true] ++ tblock q

def tcost (m q : Nat) : Nat := 12*q*q + (6*m+29)*q

theorem tblock_succ (q : Nat) : tblock (q+1) = [true,true,true] ++ tblock q := by
  rfl

theorem tcost_succ (m q : Nat) :
    tcost m (q+1) = (6*m+41) + tcost (m+4) q := by
  simp only [tcost]
  simp only [Nat.mul_add, Nat.add_mul]
  omega

theorem iter_triplet (m q : Nat) (ys : List Bool) :
    run (tcost m q) (ab m (tblock q ++ ys)) = ab (m+4*q) ys := by
  induction q generalizing m with
  | zero => simp [tcost, tblock, run]
  | succ q ih =>
    calc
      run (tcost m (q+1)) (ab m (tblock (q+1) ++ ys))
        = run ((6*m+41)+tcost (m+4) q)
          (ab m ([true,true,true] ++ (tblock q ++ ys))) := by
            rw [tcost_succ, tblock_succ]
            simp only [List.append_assoc]
      _ = run (tcost (m+4) q)
          (run (6*m+41) (ab m ([true,true,true] ++ (tblock q ++ ys)))) := run_add _ _ _
      _ = run (tcost (m+4) q) (ab (m+4) (tblock q ++ ys)) := by
            rw [triplet_pump]
      _ = ab ((m+4)+4*q) ys := ih (m+4)
      _ = ab (m+4*(q+1)) ys := by congr 1; omega

#print axioms iter_triplet
end CryptidA
