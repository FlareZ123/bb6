import Lean.Elab.Tactic.Omega
import TokenCode

namespace BB6.Parikh

def pairsN : List Bool → Nat
  | [] => 0
  | false::xs => 1 + pairsN xs
  | true::xs => pairsN xs

def triplesN : List Bool → Nat
  | [] => 0
  | false::xs => triplesN xs
  | true::xs => 1 + triplesN xs

/-- Number of ordered index pairs (i,j) where i<j, w[i]=false, w[j]=true. -/
def mixedInv : List Bool → Nat
  | [] => 0
  | false::xs => triplesN xs + mixedInv xs
  | true::xs => mixedInv xs

def triplePairs : List Bool → Nat
  | [] => 0
  | false::xs => triplePairs xs
  | true::xs => triplesN xs + triplePairs xs

def triangular : Nat → Nat
  | 0 => 0
  | n+1 => n + triangular n

theorem triplePairs_triangular (ws : List Bool) :
    triplePairs ws = triangular (triplesN ws) := by
  induction ws with
  | nil => rfl
  | cons b ws ih =>
    cases b with
    | false => simpa [triplePairs, triplesN] using ih
    | true =>
      simp only [triplePairs, triplesN, ih]
      calc
        triplesN ws + triangular (triplesN ws) =
            triangular (triplesN ws + 1) := rfl
        _ = triangular (1 + triplesN ws) := by
          congr 1 <;> omega

theorem wordInc_formula (ws : List Bool) :
    CryptidA.wordInc ws = pairsN ws + 4*triplesN ws := by
  induction ws with
  | nil => rfl
  | cons b ws ih =>
    cases b <;> simp [CryptidA.wordInc, pairsN, triplesN, ih] <;> omega

private theorem mulShift1 (m t : Nat) :
    (6*(m+1)+41)*t = (6*m+41)*t + 6*t := by
  calc
    (6*(m+1)+41)*t = ((6*m+41)+6)*t := by congr 1 <;> omega
    _ = _ := by rw [Nat.add_mul]

private theorem mulShift4 (m t : Nat) :
    (6*(m+4)+41)*t = (6*m+41)*t + 24*t := by
  calc
    (6*(m+4)+41)*t = ((6*m+41)+24)*t := by congr 1 <;> omega
    _ = _ := by rw [Nat.add_mul]

/-- Exact original-machine word cost in 3 integer statistics. -/
theorem wordCost_formula (m : Nat) (ws : List Bool) :
    CryptidA.wordCost m ws =
      2*pairsN ws + (6*m+41)*triplesN ws +
        6*mixedInv ws + 24*triplePairs ws := by
  induction ws generalizing m with
  | nil => rfl
  | cons b ws ih =>
    cases b with
    | false =>
      simp only [CryptidA.wordCost, pairsN, triplesN, mixedInv, triplePairs]
      rw [ih (m+1), mulShift1]
      omega
    | true =>
      simp only [CryptidA.wordCost, pairsN, triplesN, mixedInv, triplePairs]
      rw [ih (m+4), mulShift4]
      rw [Nat.mul_add]
      omega

theorem wordCost_closed (m : Nat) (ws : List Bool) :
    CryptidA.wordCost m ws =
      2*pairsN ws + (6*m+41)*triplesN ws +
      6*mixedInv ws + 24*triangular (triplesN ws) := by
  rw [wordCost_formula, triplePairs_triangular]

theorem equal_cost_from_counts (m : Nat) (w v : List Bool)
    (hp : pairsN w = pairsN v)
    (ht : triplesN w = triplesN v)
    (hi : mixedInv w = mixedInv v) :
    CryptidA.wordCost m w = CryptidA.wordCost m v := by
  rw [wordCost_closed, wordCost_closed, hp, ht, hi]

#print axioms wordInc_formula
#print axioms wordCost_closed
#print axioms equal_cost_from_counts
end BB6.Parikh
