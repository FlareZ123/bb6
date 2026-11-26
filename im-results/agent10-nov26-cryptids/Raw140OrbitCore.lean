import BlockMacro
namespace Raw140Orbit
open BB6BlockFAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev S := Sym.ofCode
abbrev U (a n : Nat) := List.replicate n (S a)
def boundary (q : Q) (d : Bool) (L R : List Sym) : Prim :=
  if d then render q .lo (R.headD Sym.zero) L R.tail
  else render q .hi (L.headD Sym.zero) L.tail R

theorem left_zero (q : Q) (d : Bool) (R : List Sym) : boundary q d [Sym.zero] R = boundary q d [] R := by
  cases d <;> simp [boundary, render, leftRay, Sym.zero, blank_cons]
theorem right_zero (q : Q) (d : Bool) (L : List Sym) : boundary q d L [Sym.zero] = boundary q d L [] := by
  cases d <;> simp [boundary, render, rightRay, Sym.zero, blank_cons]

theorem stepR (M : Table) (q q' : Q) (d : Bool) (a b : Sym) (k : Nat) (L R : List Sym)
    (h : blockExit M q true a = some ⟨k,q',d,b⟩) :
    run M k (boundary q true L (a::R)) = some (if d then boundary q' true (b::L) R else boundary q' false L (b::R)) := by
  have H := (macroRun_sound M 145 q .lo a L R ⟨k,q',d,b⟩ h).2
  cases d <;> exact H

theorem stepL (M : Table) (q q' : Q) (d : Bool) (a b : Sym) (k : Nat) (L R : List Sym)
    (h : blockExit M q false a = some ⟨k,q',d,b⟩) :
    run M k (boundary q false (a::L) R) = some (if d then boundary q' true (b::L) R else boundary q' false L (b::R)) := by
  have H := (macroRun_sound M 145 q .hi a L R ⟨k,q',d,b⟩ h).2
  cases d <;> exact H

theorem join {M : Table} {a b c : Prim} {m n : Nat}
    (h : run M m a = some b) (g : run M n b = some c) : run M (m+n) a = some c := by
  rw [run_add,h]; exact g

theorem sweepR (M : Table) (q : Q) (a b : Sym) (k : Nat) (n : Nat) (L R : List Sym)
    (h : blockExit M q true a = some ⟨k,q,true,b⟩) :
    run M (n*k) (boundary q true L (List.replicate n a ++ R)) = some (boundary q true (List.replicate n b ++ L) R) := by
  induction n generalizing L with
  | zero => simp [run]
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, Nat.succ_mul, Nat.add_comm (n*k) k]
    have H := join (stepR M q q true a b k L (List.replicate n a ++ R) h) (ih (b::L))
    rw [List.replicate_succ']
    simpa only [List.append_assoc,List.singleton_append] using H

theorem sweepL (M : Table) (q : Q) (a b : Sym) (k : Nat) (n : Nat) (L R : List Sym)
    (h : blockExit M q false a = some ⟨k,q,false,b⟩) :
    run M (n*k) (boundary q false (List.replicate n a ++ L) R) = some (boundary q false L (List.replicate n b ++ R)) := by
  induction n generalizing R with
  | zero => simp [run]
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, Nat.succ_mul, Nat.add_comm (n*k) k]
    have H := join (stepL M q q false a b k (List.replicate n a ++ L) R h) (ih (b::R))
    rw [List.replicate_succ']
    simpa only [List.append_assoc,List.singleton_append] using H

theorem merge (a m n : Nat) (R : List Sym) : U a m ++ (U a n ++ R) = U a (m+n) ++ R := by
  unfold U; rw [← List.append_assoc, List.replicate_append_replicate]

theorem rep_cons (a : Sym) (n : Nat) (R : List Sym) : List.replicate n a ++ a::R = a :: (List.replicate n a ++ R) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,List.cons_append,ih]
@[simp] theorem Szero : S 0 = Sym.zero := rfl

def base : Table := fun q b => match q.val,b with
 | 0,false => some ⟨true,true,1⟩
 | 1,false => some ⟨true,true,2⟩
 | 1,true => some ⟨false,false,3⟩
 | 2,false => some ⟨true,true,3⟩
 | 2,true => some ⟨false,true,0⟩
 | 3,false => some ⟨true,false,1⟩
 | 3,true => some ⟨true,false,4⟩
 | 4,false => some ⟨false,false,1⟩
 | 4,true => some ⟨false,true,4⟩
 | _,_ => none

def familyA (n : Nat) := boundary 1 true [S 5] (U 2 n ++ [S 1,S 5])
def familyB (n : Nat) := boundary 1 true [S 5] (U 2 n ++ [S 4,S 2])
end Raw140Orbit
