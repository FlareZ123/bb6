import Raw140ERSuffix

namespace Raw140ERSuffixClosed
open BB6BlockFAR Raw140Orbit Raw140Extra
open Raw140Double (Reach)
open Raw140ERSweep Raw140ERSuffix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rank : Tail → Nat
  | .t542 => 0
  | .t152 => 1
  | .t1121 => 2
  | .t5215 => 3
  | .t1155 => 4
  | .t11511 => 5

def wrap : Tail → Nat
  | .t11511 => 1
  | _ => 0

def trips133 : Nat → List Bool
  | 0 => []
  | n+1 => trips133 n ++ [false,true,true]

def rhoN : Nat → Tail → Tail
  | 0,s => s
  | n+1,s => rhoN n (rho s)

def wraps (n : Nat) (s : Tail) : Nat := (n + rank s) / 6

theorem wraps_succ (n : Nat) (s : Tail) :
    wraps (n+1) s = wraps n (rho s) + wrap s := by
  cases s <;> simp [wraps,rank,rho,wrap] <;> omega

theorem trips_wrap (k : Nat) (s : Tail) :
    trips133 (k + wrap s) = trips133 k ++ carry s := by
  cases s <;> simp [wrap,trips133,carry]

theorem iterate_closed (n : Nat) (W : List Bool) (s : Tail) :
    iterate n W s =
      (trips133 (wraps n s) ++ W ++ List.replicate n true, rhoN n s) := by
  induction n generalizing W s with
  | zero =>
      simp [iterate,wraps,rank,rhoN,trips133]
  | succ n ih =>
      rw [iterate, ih]
      have hw := wraps_succ n s
      rw [hw, trips_wrap (wraps n (rho s)) s]
      simp only [advanceWord, rhoN, List.append_assoc]
      simp only [List.replicate_succ, List.cons_append]

def sym133 : Nat → List Sym
  | 0 => []
  | n+1 => sym133 n ++ [S 1,S 3,S 3]

theorem oddword_trips133 (n : Nat) :
    oddword (trips133 n) = sym133 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [trips133, oddword_append, ih, oddword, Bool.false_eq_true,
        ite_false, ite_true, sym133]

theorem oddword_true (n : Nat) :
    oddword (List.replicate n true) = U 3 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [List.replicate_succ, oddword, ite_true, U,
        List.cons_append, ih]

theorem bank_closed (n : Nat) (W : List Bool) (X : List Sym) (s : Tail) :
    Reach base
      (boundary 4 true (S 1::(oddword W ++ U 5 n ++ X)) (tailWord s))
      (boundary 4 true
        (S 1::(sym133 (wraps n s) ++ oddword W ++ U 3 n ++ X))
        (tailWord (rhoN n s))) := by
  have h := bank n W X s
  rw [iterate_closed n W s] at h
  simpa only [oddword_append, oddword_trips133, oddword_true,
    List.append_assoc] using h

#print axioms iterate_closed
#print axioms bank_closed
end Raw140ERSuffixClosed
