import SweepPumping
namespace BB6.Agent1Raw60LCOneRecursive
open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
inductive V where | m482 | m494 | m555
  deriving DecidableEq

def table (v : V) : PartialMachine := fun (q,b) =>
  match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,if v = .m555 then 3 else 5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,if v = .m555 then 5 else 2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => none
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => if v = .m555 then some (some ⟨true,false,2⟩) else some (some ⟨true,true,3⟩)
  | 5,true => match v with
    | .m482 => some (some ⟨false,false,2⟩)
    | .m494 => some (some ⟨true,false,4⟩)
    | .m555 => some (some ⟨false,true,2⟩)
  | _,_ => none
abbrev U (n : Nat) := List.replicate n true
abbrev Q (q : Fin 6) (L R : List Bool) : Z0 := ⟨q,L,R⟩
abbrev A := Q 0
abbrev C := Q 2
abbrev F := Q 5

theorem merge (a b : Nat) (L : List Bool) : U a ++ (U b ++ L) = U (a+b) ++ L := by
  rw [← List.append_assoc,List.replicate_append_replicate]

theorem shift (a b : Nat) (L : List Bool) : U a ++ (U b ++ L) = U b ++ (U a ++ L) := by
  rw [merge,merge,Nat.add_comm a b]

theorem sweep5 (v : V) (hv : v ≠ .m555) (k : Nat) (L R : List Bool) :
    run0 (table v) k (C (U k++L) R) = some (C L (U k++R)) := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    have h : run0 (table v) 1 (C (true::(U k++L)) R) = some (C (U k++L) (true::R)) := by
      cases v <;> first | rfl | contradiction
    have H := join0 h (ih (true::R))
    rw [Nat.add_comm 1 k] at H
    have e : U k++true::R = U (k+1)++R := by rw [← merge k 1]; rfl
    rw [e] at H
    exact H

theorem clear5 (v : V) (hv : v ≠ .m555) (k : Nat) (L R : List Bool) :
    run0 (table v) (1+k) (A (true::(U k++L)) R) = some (C L (U k++false::R)) := by
  have h : run0 (table v) 1 (A (true::(U k++L)) R) = some (C (U k++L) (false::R)) := by cases v <;> rfl
  exact join0 h (sweep5 v hv k L (false::R))

def extra : V → Nat | .m482 => 3 | .m494 => 5 | .m555 => 0
def T5 (v : V) : Nat → Nat
  | 0 => 3
  | n+1 => 4*T5 v n + 3*(5*n+2) + extra v + 9

theorem fill5 (v : V) (hv : v ≠ .m555) (n : Nat) (b : Bool) (L R : List Bool) :
    run0 (table v) (T5 v n) (C (false::L) (U (5*n+2)++b::R)) =
    some (A (b::(U (5*n+2)++false::L)) R) := by
  induction n generalizing b R with
  | zero => cases v <;> cases b <;> rfl
  | succ n ih =>
    let k := 5*n+2
    have h1 := ih true (true::true::true::true::b::R)
    have h2 := clear5 v hv k (false::L) (true::true::true::true::b::R)
    have h3 := ih false (true::true::true::true::b::R)
    have h4 : run0 (table v) (extra v) (A (false::(U k++false::L)) (true::true::true::true::b::R)) =
        some (C (true::true::(U k++false::L)) (false::true::true::b::R)) := by
      cases v <;> first | rfl | contradiction
    have h5 := sweep5 v hv (k+2) (false::L) (false::true::true::b::R)
    have e : U (k+2)++false::L = true::true::(U k++false::L) := by rfl
    rw [e] at h5
    have e' : U (k+2)++false::true::true::b::R = U k++true::true::false::true::true::b::R := by
      rw [← merge k 2]; rfl
    rw [e'] at h5
    have h6 := ih true (true::false::true::true::b::R)
    have h7 := clear5 v hv k (false::L) (true::false::true::true::b::R)
    have h8 := ih false (true::false::true::true::b::R)
    have h9 : run0 (table v) 5 (A (false::(U k++false::L)) (true::false::true::true::b::R)) =
        some (A (b::(U (k+5)++false::L)) R) := by
      cases v <;> first | (cases b <;> rfl) | contradiction
    have H := join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 h1 h2) h3) h4) h5) h6) h7) h8) h9
    have ei : U k++true::true::true::true::true::b::R = U (k+5)++b::R := by
      rw [← merge k 5]; rfl
    rw [ei] at H
    have ek : k+5=5*(n+1)+2 := by dsimp [k]; omega
    rw [ek] at H
    rw [show T5 v n+(1+k)+T5 v n+extra v+(k+2)+T5 v n+(1+k)+T5 v n+5 = T5 v (n+1) by
      simp only [T5]; dsimp [k]; omega] at H
    exact H

theorem sweep4 (n : Nat) (L R : List Bool) :
    run0 (table .m555) (4*n) (C (U (2*n)++L) R) = some (C L (U (2*n)++R)) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h : run0 (table .m555) 4 (C (true::true::(U (2*n)++L)) R) = some (C (U (2*n)++L) (true::true::R)) := by rfl
    have H := join0 h (ih (true::true::R))
    have e : U (2*(n+1))++L = true::true::(U (2*n)++L) := by rfl
    rw [← e] at H
    have e' : U (2*n)++true::true::R = U (2*(n+1))++R := by rw [show 2*(n+1)=2*n+2 by omega,← merge (2*n) 2]; rfl
    rw [e',show 4+4*n=4*(n+1) by omega] at H
    exact H

theorem clear4 (n : Nat) (L R : List Bool) :
    run0 (table .m555) (1+4*n) (A (true::(U (2*n)++L)) R) = some (C L (U (2*n)++false::R)) := by
  have h : run0 (table .m555) 1 (A (true::(U (2*n)++L)) R) = some (C (U (2*n)++L) (false::R)) := by rfl
  exact join0 h (sweep4 n L (false::R))

def T4 : Nat → Nat | 0 => 3 | n+1 => 2*T4 n + (1+4*(2*n+1))+4

theorem fill4 (n : Nat) (b : Bool) (L R : List Bool) :
    run0 (table .m555) (T4 n) (C (false::L) (U (4*n+2)++b::R)) =
    some (A (b::(U (4*n+2)++false::L)) R) := by
  induction n generalizing b R with
  | zero => cases b <;> rfl
  | succ n ih =>
    let k := 4*n+2
    have h1 := ih true (true::true::true::b::R)
    have h2 := clear4 (2*n+1) (false::L) (true::true::true::b::R)
    rw [show 2*(2*n+1)=k by dsimp [k]; omega] at h2
    have h3 := ih false (true::true::true::b::R)
    have h4 : run0 (table .m555) 4 (A (false::(U k++false::L)) (true::true::true::b::R)) = some (A (b::(U (k+4)++false::L)) R) := by cases b <;> rfl
    have H := join0 (join0 (join0 h1 h2) h3) h4
    have ei : U k++true::true::true::true::b::R = U (k+4)++b::R := by rw [← merge k 4]; rfl
    rw [ei,show k+4=4*(n+1)+2 by dsimp [k]; omega] at H
    rw [show T4 n+(1+4*(2*n+1))+T4 n+4=T4 (n+1) by simp [T4]; omega] at H
    exact H
def family5 (n : Nat) : Z0 := A (false::(U (5*n+6)++[false])) []
def cost5 (v : V) (n : Nat) : Nat := 7+(1+(5*n+9))+T5 v (n+1)+(1+(5*n+7))+T5 v (n+1)+6

theorem entry5 (v : V) (hv : v ≠ .m555) :
    run0 (table v) (if v = .m482 then 64 else 66) ⟨0,[],[]⟩ = some (family5 0) := by
  cases v <;> first | rfl | contradiction

theorem growth5 (v : V) (hv : v ≠ .m555) (n : Nat) :
    run0 (table v) (cost5 v n) (family5 n) = some (family5 (n+1)) := by
  let k := 5*n+7
  have h1 : run0 (table v) 7 (family5 n) = some (A (true::(U (5*n+9)++[false])) []) := by
    cases v <;> first | rfl | contradiction
  have h2 := clear5 v hv (5*n+9) [false] []
  have he : U (5*n+9)++[false] = U k++[true,true,false] := by
    rw [show 5*n+9=k+2 by dsimp [k],← merge k 2]; rfl
  rw [he] at h1 h2
  have h3 := fill5 v hv (n+1) true [] [true,false]
  have hk : 5*(n+1)+2=k := by dsimp [k]; omega
  rw [hk] at h3
  have h4 := clear5 v hv k [false] [true,false]
  have h5 := fill5 v hv (n+1) false [] [true,false]
  rw [hk] at h5
  have h6 : run0 (table v) 6 (A (false::(U k++[false])) [true,false]) = some (family5 (n+1)) := by
    unfold family5
    rw [show 5*(n+1)+6=k+4 by dsimp [k]; omega]
    cases v <;> first | rfl | contradiction
  exact join0 (join0 (join0 (join0 (join0 h1 h2) h3) h4) h5) h6

def family4 (n : Nat) : Z0 := A (false::(U (4*n+5)++[false])) []
def cost4 (n : Nat) : Nat := 7+(1+4*(2*n+4))+T4 (n+1)+(1+4*(2*n+3))+T4 (n+1)+5

theorem entry4 : run0 (table .m555) 30 ⟨0,[],[]⟩ = some (family4 0) := by rfl

theorem growth4 (n : Nat) :
    run0 (table .m555) (cost4 n) (family4 n) = some (family4 (n+1)) := by
  let k := 4*n+6
  have h1 : run0 (table .m555) 7 (family4 n) = some (A (true::(U (4*n+8)++[false])) []) := by rfl
  have h2 := clear4 (2*n+4) [false] []
  rw [show 2*(2*n+4)=4*n+8 by omega] at h2
  have he : U (4*n+8)++[false] = U k++[true,true,false] := by
    rw [show 4*n+8=k+2 by dsimp [k],← merge k 2]; rfl
  rw [he] at h1 h2
  have h3 := fill4 (n+1) true [] [true,false]
  have hk : 4*(n+1)+2=k := by dsimp [k]; omega
  rw [hk] at h3
  have h4 := clear4 (2*n+3) [false] [true,false]
  rw [show 2*(2*n+3)=k by dsimp [k]; omega] at h4
  have h5 := fill4 (n+1) false [] [true,false]
  rw [hk] at h5
  have h6 : run0 (table .m555) 5 (A (false::(U k++[false])) [true,false]) = some (family4 (n+1)) := by
    unfold family4
    rw [show 4*(n+1)+5=k+3 by dsimp [k]; omega]
    rfl
  exact join0 (join0 (join0 (join0 (join0 h1 h2) h3) h4) h5) h6
#print axioms growth5
#print axioms growth4
#print axioms fill5
#print axioms fill4
namespace M482
def table : PartialMachine := BB6.Agent1Raw60LCOneRecursive.table .m482
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family5 64 (cost5 .m482) (entry5 .m482 (by decide)) (by intro n; unfold cost5; omega) (growth5 .m482 (by decide)) m hm
#print axioms never
end M482
namespace M494
def table : PartialMachine := BB6.Agent1Raw60LCOneRecursive.table .m494
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family5 66 (cost5 .m494) (entry5 .m494 (by decide)) (by intro n; unfold cost5; omega) (growth5 .m494 (by decide)) m hm
#print axioms never
end M494
namespace M555
def table : PartialMachine := BB6.Agent1Raw60LCOneRecursive.table .m555
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family4 30 cost4 entry4 (by intro n; unfold cost4; omega) growth4 m hm
#print axioms never
end M555
end BB6.Agent1Raw60LCOneRecursive
