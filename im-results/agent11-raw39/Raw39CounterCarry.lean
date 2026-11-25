import SweepPumping
open BB6Coverage BB6Coverage.Agent31Pump
namespace BB6.Agent11CounterCarry

def fillCost (c : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => fillCost c n + c n + fillCost c n

theorem rep_succ_snoc (W : List Bool) (n : Nat) : rep W (n+1) = rep W n ++ W := by
  rw [rep_snoc]; rfl

/-- One arbitrary-tail carry lemma proves an entire binary-counting epoch. -/
theorem fill (p : PartialMachine) (Q : List Bool → Z0) (A Z : List Bool) (c : Nat → Nat)
    (carry : ∀ n R, run0 p (c n) (Q (rep A n ++ Z ++ R)) = some (Q (rep Z n ++ A ++ R)))
    (n : Nat) (R : List Bool) : run0 p (fillCost c n) (Q (rep Z n ++ R)) = some (Q (rep A n ++ R)) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    rw [rep_succ_snoc Z n,rep_succ_snoc A n]
    simp only [List.append_assoc,fillCost]
    exact join0 (join0 (ih (Z++R)) (by simpa only [List.append_assoc] using carry n R)) (ih (A++R))

def partialCost (c : Nat → Nat) (k : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => partialCost c k n + c (k+n) + fillCost c (k+n)

theorem rep_add (W : List Bool) (k n : Nat) : rep W (k+n) = rep W k ++ rep W n := by
  induction n with
  | zero => simp [rep]
  | succ n ih => rw [Nat.add_succ,rep_succ_snoc,rep_succ_snoc W n,ih,List.append_assoc]

/-- The same epoch starting with the lowest k bits already set. -/
theorem fillFrom (p : PartialMachine) (Q : List Bool → Z0) (A Z : List Bool) (c : Nat → Nat)
    (carry : ∀ n R, run0 p (c n) (Q (rep A n ++ Z ++ R)) = some (Q (rep Z n ++ A ++ R)))
    (k n : Nat) (R : List Bool) : run0 p (partialCost c k n) (Q (rep A k ++ rep Z n ++ R)) = some (Q (rep A (k+n) ++ R)) := by
  induction n generalizing R with
  | zero => simp [partialCost,rep,run0]
  | succ n ih =>
    change run0 p (partialCost c k (n+1)) (Q (rep A k ++ rep Z (n+1) ++ R)) = some (Q (rep A ((k+n)+1) ++ R))
    rw [rep_succ_snoc Z n,rep_succ_snoc A (k+n)]
    simp only [List.append_assoc,partialCost]
    have h1 := ih (Z++R)
    have h2 := carry (k+n) R
    have h3 := fill p Q A Z c carry (k+n) (A++R)
    simp only [List.append_assoc] at h1 h2 h3
    exact join0 (join0 h1 h2) h3

#print axioms fill
#print axioms fillFrom
end BB6.Agent11CounterCarry
