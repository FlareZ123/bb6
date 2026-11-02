import TripleUniversal
import TenPump

namespace CryptidA

def wordCode : List Bool → List Bool
  | [] => []
  | false :: xs => [true,false] ++ wordCode xs
  | true :: xs => [true,true,true] ++ wordCode xs

def wordInc : List Bool → Nat
  | [] => 0
  | false :: xs => 1 + wordInc xs
  | true :: xs => 4 + wordInc xs

def wordCost : Nat → List Bool → Nat
  | _, [] => 0
  | m, false :: xs => 2 + wordCost (m+1) xs
  | m, true :: xs => (6*m+41) + wordCost (m+4) xs

theorem consume_code (m : Nat) (ws ys : List Bool) :
    run (wordCost m ws) (ab m (wordCode ws ++ ys)) =
      ab (m+wordInc ws) ys := by
  induction ws generalizing m with
  | nil => simp [run, wordCost, wordCode, wordInc]
  | cons b ws ih =>
    cases b with
    | false =>
      calc
        run (wordCost m (false :: ws)) (ab m (wordCode (false :: ws) ++ ys))
            = run (2+wordCost (m+1) ws) (ab m ([true,false] ++ (wordCode ws ++ ys))) := by
                simp only [wordCode, wordCost, List.append_assoc]
        _ = run (wordCost (m+1) ws) (run 2 (ab m ([true,false] ++ (wordCode ws ++ ys)))) := run_add _ _ _
        _ = run (wordCost (m+1) ws) (ab (m+1) (wordCode ws ++ ys)) := by rw [ten_pump]
        _ = ab ((m+1)+wordInc ws) ys := ih (m+1)
        _ = ab (m+wordInc (false :: ws)) ys := by simp [wordInc]; congr 1; omega
    | true =>
      calc
        run (wordCost m (true :: ws)) (ab m (wordCode (true :: ws) ++ ys))
            = run ((6*m+41)+wordCost (m+4) ws) (ab m ([true,true,true] ++ (wordCode ws ++ ys))) := by
                simp only [wordCode, wordCost, List.append_assoc]
        _ = run (wordCost (m+4) ws) (run (6*m+41) (ab m ([true,true,true] ++ (wordCode ws ++ ys)))) := run_add _ _ _
        _ = run (wordCost (m+4) ws) (ab (m+4) (wordCode ws ++ ys)) := by rw [triplet_pump]
        _ = ab ((m+4)+wordInc ws) ys := ih (m+4)
        _ = ab (m+wordInc (true :: ws)) ys := by simp [wordInc]; congr 1; omega

#print axioms consume_code
end CryptidA
