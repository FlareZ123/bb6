import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw121QuadraticExtra
open BB6Coverage BB6Coverage.Agent31Pump

theorem repReplicate (b : Bool) (k n : Nat) :
    rep (List.replicate k b) n = List.replicate (k*n) b := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep,ih,List.replicate_append_replicate,show k+k*n=k*(n+1) by rw [Nat.mul_succ,Nat.add_comm]]

theorem replicateAddTail (b : Bool) (a c : Nat) (R : List Bool) :
    List.replicate a b ++ (List.replicate c b ++ R) = List.replicate (a+c) b ++ R := by
  rw [← List.append_assoc,List.replicate_append_replicate]


def innerCost (b s : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => b+s*n+innerCost b s n

theorem innerAll (p : PartialMachine) (M : Nat → Nat → Z0) (b s : Nat)
    (one : ∀ n j, run0 p (b+s*n) (M (n+1) j) = some (M n (j+1)))
    (n j : Nat) : run0 p (innerCost b s n) (M n j) = some (M 0 (j+n)) := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    have H := join0 (one n j) (ih (j+1))
    simpa only [innerCost,show j+1+n=j+(n+1) by omega] using H

def epochCost (a s b u c v n : Nat) := a+s*n+innerCost b u n+(c+v*n)

theorem growthAll (p : PartialMachine) (F : Nat → Z0) (M : Nat → Nat → Z0) (a s b u c v : Nat)
    (first : ∀ n, run0 p (a+s*n) (F n) = some (M n 0))
    (one : ∀ n j, run0 p (b+u*n) (M (n+1) j) = some (M n (j+1)))
    (last : ∀ j, run0 p (c+v*j) (M 0 j) = some (F (j+1)))
    (n : Nat) : run0 p (epochCost a s b u c v n) (F n) = some (F (n+1)) := by
  have H := join0 (first n) (innerAll p M b u one n 0)
  rw [Nat.zero_add] at H
  exact join0 H (last n)


namespace M318

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

theorem firstStep0 (n : Nat) : run0 table 1 ⟨4, ([false,true,true,true,true,true,true,true]) ++ ((rep [true,true,true] n)), []⟩ = some ⟨0, ([true,true,true,true,true,true,true]) ++ ((rep [true,true,true] n)), ([false])⟩ := by rfl

theorem firstLocal1 (L R : List Bool) : run0 table 3 ⟨0, ([true,true,true,true,true,true,true]) ++ (([true,true,true]) ++ ((L))), (R)⟩ = some ⟨0, ([true,true,true,true,true,true,true]) ++ ((L)), ([true,true,true]) ++ ((R))⟩ := by rfl

theorem firstStep1 (n : Nat) : run0 table (3*n) ⟨0, ([true,true,true,true,true,true,true]) ++ ((rep [true,true,true] n)), ([false])⟩ = some ⟨0, ([true,true,true,true,true,true,true]), (rep [true,true,true] n) ++ (([false]))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 0 [true,true,true,true,true,true,true] [] [true,true,true] [true,true,true] 3 firstLocal1 n ([]) (([false]))

theorem firstStep2 (n : Nat) : run0 table 16 ⟨0, ([true,true,true,true,true,true,true]), (rep [true,true,true] n) ++ (([false]))⟩ = some ⟨4, ([true,true,false,true,true,true]), ([true,true]) ++ ((rep [true,true,true] n) ++ (([false])))⟩ := by rfl

theorem firstLocal3 (L R : List Bool) : run0 table 3 ⟨4, ([true]) ++ ((L)), ([true,true]) ++ (([true,true,true]) ++ ((R)))⟩ = some ⟨4, ([true]) ++ (([true,true,true]) ++ ((L))), ([true,true]) ++ ((R))⟩ := by rfl

theorem firstStep3 (n : Nat) : run0 table (3*n) ⟨4, ([true,true,false,true,true,true]), ([true,true]) ++ ((rep [true,true,true] n) ++ (([false])))⟩ = some ⟨4, ([true]) ++ ((rep [true,true,true] n) ++ (([true,false,true,true,true]))), ([true,true,false])⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [true,true] [true,true,true] [true,true,true] 3 firstLocal3 n (([true,false,true,true,true])) (([false]))

theorem firstStep4 (n : Nat) : run0 table 3 ⟨4, ([true]) ++ ((rep [true,true,true] n) ++ (([true,false,true,true,true]))), ([true,true,false])⟩ = some ⟨4, ([false,true,true,true]) ++ ((rep [true,true,true] n) ++ (([true,false,true,true,true]))), []⟩ := by rfl

theorem firstEqL (n : Nat) : (([false,true,true,true]) ++ ((rep [true,true,true] n) ++ (([true,false,true,true,true])))) = (([false,true,true,true,true]) ++ ((rep [true,true,true] n) ++ (([false,true,true,true])))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 3 true) ++ ((rep (List.replicate 3 true) n) ++ ((List.replicate 1 true) ++ ((List.replicate 1 false) ++ ((List.replicate 3 true))))))) = ((List.replicate 1 false) ++ ((List.replicate 4 true) ++ ((rep (List.replicate 3 true) n) ++ ((List.replicate 1 false) ++ ((List.replicate 3 true))))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem firstRaw (n : Nat) : run0 table (20+6*n) ⟨4, ([false,true,true,true,true,true,true,true]) ++ ((rep [true,true,true] n)), []⟩ = some ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true,true] n) ++ (([false,true,true,true]))), []⟩ := by

  have H := firstStep0 n

  have H := join0 H (firstStep1 n)

  have H := join0 H (firstStep2 n)

  have H := join0 H (firstStep3 n)

  have H := join0 H (firstStep4 n)

  rw [show 1+3*n+16+3*n+3 = 20+6*n by omega] at H

  rw [firstEqL n] at H

  exact H

theorem innerStep0 (n j : Nat) : run0 table 1 ⟨4, ([false,true,true,true,true,true,true,true]) ++ ((rep [true,true,true] n) ++ (([false,true,true,true]) ++ ((rep [true,true,true] j)))), []⟩ = some ⟨0, ([true,true,true,true,true,true,true]) ++ ((rep [true,true,true] n) ++ (([false,true,true,true]) ++ ((rep [true,true,true] j)))), ([false])⟩ := by rfl

theorem innerLocal1 (L R : List Bool) : run0 table 3 ⟨0, ([true,true,true,true,true,true,true]) ++ (([true,true,true]) ++ ((L))), (R)⟩ = some ⟨0, ([true,true,true,true,true,true,true]) ++ ((L)), ([true,true,true]) ++ ((R))⟩ := by rfl

theorem innerStep1 (n j : Nat) : run0 table (3*n) ⟨0, ([true,true,true,true,true,true,true]) ++ ((rep [true,true,true] n) ++ (([false,true,true,true]) ++ ((rep [true,true,true] j)))), ([false])⟩ = some ⟨0, ([true,true,true,true,true,true,true,false,true,true,true]) ++ ((rep [true,true,true] j)), (rep [true,true,true] n) ++ (([false]))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 0 [true,true,true,true,true,true,true] [] [true,true,true] [true,true,true] 3 innerLocal1 n (([false,true,true,true]) ++ ((rep [true,true,true] j))) (([false]))

theorem innerStep2 (n j : Nat) : run0 table 16 ⟨0, ([true,true,true,true,true,true,true,false,true,true,true]) ++ ((rep [true,true,true] j)), (rep [true,true,true] n) ++ (([false]))⟩ = some ⟨4, ([true,true,false,true,true,true,true,true,true]) ++ ((rep [true,true,true] j)), ([true,true]) ++ ((rep [true,true,true] n) ++ (([false])))⟩ := by rfl

theorem innerLocal3 (L R : List Bool) : run0 table 3 ⟨4, ([true]) ++ ((L)), ([true,true]) ++ (([true,true,true]) ++ ((R)))⟩ = some ⟨4, ([true]) ++ (([true,true,true]) ++ ((L))), ([true,true]) ++ ((R))⟩ := by rfl

theorem innerStep3 (n j : Nat) : run0 table (3*n) ⟨4, ([true,true,false,true,true,true,true,true,true]) ++ ((rep [true,true,true] j)), ([true,true]) ++ ((rep [true,true,true] n) ++ (([false])))⟩ = some ⟨4, ([true]) ++ ((rep [true,true,true] n) ++ (([true,false,true,true,true,true,true,true]) ++ ((rep [true,true,true] j)))), ([true,true,false])⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [true,true] [true,true,true] [true,true,true] 3 innerLocal3 n (([true,false,true,true,true,true,true,true]) ++ ((rep [true,true,true] j))) (([false]))

theorem innerStep4 (n j : Nat) : run0 table 3 ⟨4, ([true]) ++ ((rep [true,true,true] n) ++ (([true,false,true,true,true,true,true,true]) ++ ((rep [true,true,true] j)))), ([true,true,false])⟩ = some ⟨4, ([false,true,true,true]) ++ ((rep [true,true,true] n) ++ (([true,false,true,true,true,true,true,true]) ++ ((rep [true,true,true] j)))), []⟩ := by rfl

theorem innerEqL (n j : Nat) : (([false,true,true,true]) ++ ((rep [true,true,true] n) ++ (([true,false,true,true,true,true,true,true]) ++ ((rep [true,true,true] j))))) = (([false,true,true,true,true]) ++ ((rep [true,true,true] n) ++ (([false,true,true,true,true,true,true]) ++ ((rep [true,true,true] j))))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 3 true) ++ ((rep (List.replicate 3 true) n) ++ ((List.replicate 1 true) ++ ((List.replicate 1 false) ++ ((List.replicate 6 true) ++ ((rep (List.replicate 3 true) j)))))))) = ((List.replicate 1 false) ++ ((List.replicate 4 true) ++ ((rep (List.replicate 3 true) n) ++ ((List.replicate 1 false) ++ ((List.replicate 6 true) ++ ((rep (List.replicate 3 true) j)))))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem innerRaw (n j : Nat) : run0 table (20+6*n) ⟨4, ([false,true,true,true,true,true,true,true]) ++ ((rep [true,true,true] n) ++ (([false,true,true,true]) ++ ((rep [true,true,true] j)))), []⟩ = some ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true,true] n) ++ (([false,true,true,true,true,true,true]) ++ ((rep [true,true,true] j)))), []⟩ := by

  have H := innerStep0 n j

  have H := join0 H (innerStep1 n j)

  have H := join0 H (innerStep2 n j)

  have H := join0 H (innerStep3 n j)

  have H := join0 H (innerStep4 n j)

  rw [show 1+3*n+16+3*n+3 = 20+6*n by omega] at H

  rw [innerEqL n j] at H

  exact H

theorem finishStep0 (j : Nat) : run0 table 26 ⟨4, ([false,true,true,true,true,false,true,true,true]) ++ ((rep [true,true,true] j)), []⟩ = some ⟨4, ([false,true,true,true,true,true,true,true,true,true,true]) ++ ((rep [true,true,true] j)), []⟩ := by rfl

theorem finishRaw (j : Nat) : run0 table (26) ⟨4, ([false,true,true,true,true,false,true,true,true]) ++ ((rep [true,true,true] j)), []⟩ = some ⟨4, ([false,true,true,true,true,true,true,true,true,true,true]) ++ ((rep [true,true,true] j)), []⟩ := by

  have H := finishStep0 j

  rw [show 26 = 26 by omega] at H

  exact H

abbrev P := [true,true,true]
def family (n : Nat) : Z0 := ⟨4,[false,true,true,true,true,true,true,true]++rep P n,[]⟩
def middle (n j : Nat) : Z0 := ⟨4,[false,true,true,true,true]++rep P n++[false,true,true,true]++rep P j,[]⟩

theorem first (n : Nat) : run0 table (20+6*n) (family n) = some (middle n 0) := by
  simpa only [family,middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using firstRaw n

theorem inner (n j : Nat) : run0 table (20+6*n) (middle (n+1) j) = some (middle n (j+1)) := by
  simpa only [middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using innerRaw n j

theorem finish (j : Nat) : run0 table (26+0*j) (middle 0 j) = some (family (j+1)) := by
  simpa only [family,middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append,Nat.one_mul,Nat.zero_mul,Nat.add_zero] using finishRaw j

def cost := epochCost 20 6 20 6 26 0
theorem entry : run0 table 34 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) :=
  growthAll table family middle 20 6 20 6 26 0 first inner finish n


theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 34 cost entry (by intro n; unfold cost epochCost; omega) growth m hm
#print axioms never

#print axioms growth
end M318

namespace M9650

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

theorem firstStep0 (n : Nat) : run0 table 3 ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n)), []⟩ = some ⟨1, ([true,true]) ++ ((rep [true,true] n)), ([false,false,true])⟩ := by rfl

theorem firstLocal1 (L R : List Bool) : run0 table 6 ⟨1, ([true,true]) ++ (([true,true]) ++ ((L))), ([false]) ++ ((R))⟩ = some ⟨1, ([true,true]) ++ ((L)), ([false]) ++ (([true,true]) ++ ((R)))⟩ := by rfl

theorem firstStep1 (n : Nat) : run0 table (6*n) ⟨1, ([true,true]) ++ ((rep [true,true] n)), ([false,false,true])⟩ = some ⟨1, ([true,true]), ([false]) ++ ((rep [true,true] n) ++ (([false,true])))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 1 [true,true] [false] [true,true] [true,true] 6 firstLocal1 n ([]) (([false,true]))

theorem firstStep2 (n : Nat) : run0 table 9 ⟨1, ([true,true]), ([false]) ++ ((rep [true,true] n) ++ (([false,true])))⟩ = some ⟨4, ([true,true,false,true]), (rep [true,true] n) ++ (([false,true]))⟩ := by rfl

theorem firstLocal3 (L R : List Bool) : run0 table 2 ⟨4, ([true]) ++ ((L)), ([true,true]) ++ ((R))⟩ = some ⟨4, ([true]) ++ (([true,true]) ++ ((L))), (R)⟩ := by rfl

theorem firstStep3 (n : Nat) : run0 table (2*n) ⟨4, ([true,true,false,true]), (rep [true,true] n) ++ (([false,true]))⟩ = some ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([false,true])⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [] [true,true] [true,true] 2 firstLocal3 n (([true,false,true])) (([false,true]))

theorem firstStep4 (n : Nat) : run0 table 1 ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([false,true])⟩ = some ⟨4, ([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([true])⟩ := by rfl

theorem firstEqL (n : Nat) : (([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true])))) = (([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true])))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 1 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 true) ++ ((List.replicate 1 false) ++ ((List.replicate 1 true))))))) = ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 false) ++ ((List.replicate 1 true))))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem firstRaw (n : Nat) : run0 table (13+8*n) ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n)), []⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true]))), ([true])⟩ := by

  have H := firstStep0 n

  have H := join0 H (firstStep1 n)

  have H := join0 H (firstStep2 n)

  have H := join0 H (firstStep3 n)

  have H := join0 H (firstStep4 n)

  rw [show 3+6*n+9+2*n+1 = 13+8*n by omega] at H

  rw [firstEqL n] at H

  exact H

theorem innerStep0 (n j : Nat) : run0 table 3 ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true]) ++ ((rep [true] j))⟩ = some ⟨1, ([true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([false,false,true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem innerLocal1 (L R : List Bool) : run0 table 6 ⟨1, ([true,true]) ++ (([true,true]) ++ ((L))), ([false]) ++ ((R))⟩ = some ⟨1, ([true,true]) ++ ((L)), ([false]) ++ (([true,true]) ++ ((R)))⟩ := by rfl

theorem innerStep1 (n j : Nat) : run0 table (6*n) ⟨1, ([true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([false,false,true,true]) ++ ((rep [true] j))⟩ = some ⟨1, ([true,true,false,true]) ++ ((rep [true] j)), ([false]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j))))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 1 [true,true] [false] [true,true] [true,true] 6 innerLocal1 n (([false,true]) ++ ((rep [true] j))) (([false,true,true]) ++ ((rep [true] j)))

theorem innerStep2 (n j : Nat) : run0 table 9 ⟨1, ([true,true,false,true]) ++ ((rep [true] j)), ([false]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j))))⟩ = some ⟨4, ([true,true,false,true,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ := by rfl

theorem innerLocal3 (L R : List Bool) : run0 table 2 ⟨4, ([true]) ++ ((L)), ([true,true]) ++ ((R))⟩ = some ⟨4, ([true]) ++ (([true,true]) ++ ((L))), (R)⟩ := by rfl

theorem innerStep3 (n j : Nat) : run0 table (2*n) ⟨4, ([true,true,false,true,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ = some ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [] [true,true] [true,true] 2 innerLocal3 n (([true,false,true,true]) ++ ((rep [true] j))) (([false,true,true]) ++ ((rep [true] j)))

theorem innerStep4 (n j : Nat) : run0 table 1 ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem innerEqL (n j : Nat) : (([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j))))) = (([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j))))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 1 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 true) ++ ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 1 true) j)))))))) = ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 1 true) j)))))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem innerRaw (n j : Nat) : run0 table (13+8*n) ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))), ([true,true]) ++ ((rep [true] j))⟩ := by

  have H := innerStep0 n j

  have H := join0 H (innerStep1 n j)

  have H := join0 H (innerStep2 n j)

  have H := join0 H (innerStep3 n j)

  have H := join0 H (innerStep4 n j)

  rw [show 3+6*n+9+2*n+1 = 13+8*n by omega] at H

  rw [innerEqL n j] at H

  exact H

theorem finishStep0 (j : Nat) : run0 table 8 ⟨4, ([false,true,true,false,true]) ++ ((rep [true] j)), ([true]) ++ ((rep [true] j))⟩ = some ⟨4, ([true,true,true]) ++ ((rep [true] j)), ([true,true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem finishLocal1 (L R : List Bool) : run0 table 1 ⟨4, ([true]) ++ ((L)), ([true,true,true]) ++ (([true]) ++ ((R)))⟩ = some ⟨4, ([true]) ++ (([true]) ++ ((L))), ([true,true,true]) ++ ((R))⟩ := by rfl

theorem finishStep1 (j : Nat) : run0 table (1*j) ⟨4, ([true,true,true]) ++ ((rep [true] j)), ([true,true,true]) ++ ((rep [true] j))⟩ = some ⟨4, ([true]) ++ ((rep [true] j) ++ (([true,true]) ++ ((rep [true] j)))), ([true,true,true])⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [true,true,true] [true] [true] 1 finishLocal1 j (([true,true]) ++ ((rep [true] j))) ([])

theorem finishStep2 (j : Nat) : run0 table 4 ⟨4, ([true]) ++ ((rep [true] j) ++ (([true,true]) ++ ((rep [true] j)))), ([true,true,true])⟩ = some ⟨4, ([false,true,true,true,true]) ++ ((rep [true] j) ++ (([true,true]) ++ ((rep [true] j)))), []⟩ := by rfl

theorem finishEqL (j : Nat) : (([false,true,true,true,true]) ++ ((rep [true] j) ++ (([true,true]) ++ ((rep [true] j))))) = (([false,true,true,true,true,true,true]) ++ ((rep [true,true] j))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 4 true) ++ ((rep (List.replicate 1 true) j) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 1 true) j)))))) = ((List.replicate 1 false) ++ ((List.replicate 6 true) ++ ((rep (List.replicate 2 true) j))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem finishRaw (j : Nat) : run0 table (12+1*j) ⟨4, ([false,true,true,false,true]) ++ ((rep [true] j)), ([true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true,true,true,true,true,true]) ++ ((rep [true,true] j)), []⟩ := by

  have H := finishStep0 j

  have H := join0 H (finishStep1 j)

  have H := join0 H (finishStep2 j)

  rw [show 8+1*j+4 = 12+1*j by omega] at H

  rw [finishEqL j] at H

  exact H

abbrev P := [true,true]
abbrev U := [true]
def family (n : Nat) : Z0 := ⟨4,false::rep P (n+2),[]⟩
def middle (n j : Nat) : Z0 := ⟨4,false::(rep P (n+1)++false::rep U (j+1)),rep U (j+1)⟩


theorem first (n : Nat) : run0 table (13+8*n) (family n) = some (middle n 0) := by
  simpa only [family,middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using firstRaw n

theorem inner (n j : Nat) : run0 table (13+8*n) (middle (n+1) j) = some (middle n (j+1)) := by
  simpa only [middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using innerRaw n j

theorem finish (j : Nat) : run0 table (12+1*j) (middle 0 j) = some (family (j+1)) := by
  simpa only [family,middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append,Nat.one_mul,Nat.zero_mul,Nat.add_zero] using finishRaw j

def cost := epochCost 13 8 13 8 12 1
theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) :=
  growthAll table family middle 13 8 13 8 12 1 first inner finish n


theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 cost entry (by intro n; unfold cost epochCost; omega) growth m hm
#print axioms never

#print axioms growth
end M9650

namespace M9651

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

theorem firstStep0 (n : Nat) : run0 table 2 ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n)), []⟩ = some ⟨0, ([true,true,true]) ++ ((rep [true,true] n)), ([false,true])⟩ := by rfl

theorem firstLocal1 (L R : List Bool) : run0 table 4 ⟨0, ([true,true,true]) ++ (([true,true]) ++ ((L))), (R)⟩ = some ⟨0, ([true,true,true]) ++ ((L)), ([true,true]) ++ ((R))⟩ := by rfl

theorem firstStep1 (n : Nat) : run0 table (4*n) ⟨0, ([true,true,true]) ++ ((rep [true,true] n)), ([false,true])⟩ = some ⟨0, ([true,true,true]), (rep [true,true] n) ++ (([false,true]))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 0 [true,true,true] [] [true,true] [true,true] 4 firstLocal1 n ([]) (([false,true]))

theorem firstStep2 (n : Nat) : run0 table 8 ⟨0, ([true,true,true]), (rep [true,true] n) ++ (([false,true]))⟩ = some ⟨4, ([true,true,false,true]), (rep [true,true] n) ++ (([false,true]))⟩ := by rfl

theorem firstLocal3 (L R : List Bool) : run0 table 2 ⟨4, ([true]) ++ ((L)), ([true,true]) ++ ((R))⟩ = some ⟨4, ([true]) ++ (([true,true]) ++ ((L))), (R)⟩ := by rfl

theorem firstStep3 (n : Nat) : run0 table (2*n) ⟨4, ([true,true,false,true]), (rep [true,true] n) ++ (([false,true]))⟩ = some ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([false,true])⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [] [true,true] [true,true] 2 firstLocal3 n (([true,false,true])) (([false,true]))

theorem firstStep4 (n : Nat) : run0 table 1 ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([false,true])⟩ = some ⟨4, ([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([true])⟩ := by rfl

theorem firstEqL (n : Nat) : (([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true])))) = (([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true])))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 1 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 true) ++ ((List.replicate 1 false) ++ ((List.replicate 1 true))))))) = ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 false) ++ ((List.replicate 1 true))))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem firstRaw (n : Nat) : run0 table (11+6*n) ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n)), []⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true]))), ([true])⟩ := by

  have H := firstStep0 n

  have H := join0 H (firstStep1 n)

  have H := join0 H (firstStep2 n)

  have H := join0 H (firstStep3 n)

  have H := join0 H (firstStep4 n)

  rw [show 2+4*n+8+2*n+1 = 11+6*n by omega] at H

  rw [firstEqL n] at H

  exact H

theorem innerStep0 (n j : Nat) : run0 table 2 ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true]) ++ ((rep [true] j))⟩ = some ⟨0, ([true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem innerLocal1 (L R : List Bool) : run0 table 4 ⟨0, ([true,true,true]) ++ (([true,true]) ++ ((L))), (R)⟩ = some ⟨0, ([true,true,true]) ++ ((L)), ([true,true]) ++ ((R))⟩ := by rfl

theorem innerStep1 (n j : Nat) : run0 table (4*n) ⟨0, ([true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ = some ⟨0, ([true,true,true,false,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 0 [true,true,true] [] [true,true] [true,true] 4 innerLocal1 n (([false,true]) ++ ((rep [true] j))) (([false,true,true]) ++ ((rep [true] j)))

theorem innerStep2 (n j : Nat) : run0 table 8 ⟨0, ([true,true,true,false,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ = some ⟨4, ([true,true,false,true,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ := by rfl

theorem innerLocal3 (L R : List Bool) : run0 table 2 ⟨4, ([true]) ++ ((L)), ([true,true]) ++ ((R))⟩ = some ⟨4, ([true]) ++ (([true,true]) ++ ((L))), (R)⟩ := by rfl

theorem innerStep3 (n j : Nat) : run0 table (2*n) ⟨4, ([true,true,false,true,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ = some ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [] [true,true] [true,true] 2 innerLocal3 n (([true,false,true,true]) ++ ((rep [true] j))) (([false,true,true]) ++ ((rep [true] j)))

theorem innerStep4 (n j : Nat) : run0 table 1 ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem innerEqL (n j : Nat) : (([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j))))) = (([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j))))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 1 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 true) ++ ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 1 true) j)))))))) = ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 1 true) j)))))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem innerRaw (n j : Nat) : run0 table (11+6*n) ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))), ([true,true]) ++ ((rep [true] j))⟩ := by

  have H := innerStep0 n j

  have H := join0 H (innerStep1 n j)

  have H := join0 H (innerStep2 n j)

  have H := join0 H (innerStep3 n j)

  have H := join0 H (innerStep4 n j)

  rw [show 2+4*n+8+2*n+1 = 11+6*n by omega] at H

  rw [innerEqL n j] at H

  exact H

theorem finishStep0 (j : Nat) : run0 table 8 ⟨4, ([false,true,true,false,true]) ++ ((rep [true] j)), ([true]) ++ ((rep [true] j))⟩ = some ⟨4, ([true,true,true]) ++ ((rep [true] j)), ([true,true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem finishLocal1 (L R : List Bool) : run0 table 1 ⟨4, ([true]) ++ ((L)), ([true,true,true]) ++ (([true]) ++ ((R)))⟩ = some ⟨4, ([true]) ++ (([true]) ++ ((L))), ([true,true,true]) ++ ((R))⟩ := by rfl

theorem finishStep1 (j : Nat) : run0 table (1*j) ⟨4, ([true,true,true]) ++ ((rep [true] j)), ([true,true,true]) ++ ((rep [true] j))⟩ = some ⟨4, ([true]) ++ ((rep [true] j) ++ (([true,true]) ++ ((rep [true] j)))), ([true,true,true])⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [true,true,true] [true] [true] 1 finishLocal1 j (([true,true]) ++ ((rep [true] j))) ([])

theorem finishStep2 (j : Nat) : run0 table 4 ⟨4, ([true]) ++ ((rep [true] j) ++ (([true,true]) ++ ((rep [true] j)))), ([true,true,true])⟩ = some ⟨4, ([false,true,true,true,true]) ++ ((rep [true] j) ++ (([true,true]) ++ ((rep [true] j)))), []⟩ := by rfl

theorem finishEqL (j : Nat) : (([false,true,true,true,true]) ++ ((rep [true] j) ++ (([true,true]) ++ ((rep [true] j))))) = (([false,true,true,true,true,true,true]) ++ ((rep [true,true] j))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 4 true) ++ ((rep (List.replicate 1 true) j) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 1 true) j)))))) = ((List.replicate 1 false) ++ ((List.replicate 6 true) ++ ((rep (List.replicate 2 true) j))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem finishRaw (j : Nat) : run0 table (12+1*j) ⟨4, ([false,true,true,false,true]) ++ ((rep [true] j)), ([true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true,true,true,true,true,true]) ++ ((rep [true,true] j)), []⟩ := by

  have H := finishStep0 j

  have H := join0 H (finishStep1 j)

  have H := join0 H (finishStep2 j)

  rw [show 8+1*j+4 = 12+1*j by omega] at H

  rw [finishEqL j] at H

  exact H

abbrev P := [true,true]
abbrev U := [true]
def family (n : Nat) : Z0 := ⟨4,false::rep P (n+2),[]⟩
def middle (n j : Nat) : Z0 := ⟨4,false::(rep P (n+1)++false::rep U (j+1)),rep U (j+1)⟩


theorem first (n : Nat) : run0 table (11+6*n) (family n) = some (middle n 0) := by
  simpa only [family,middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using firstRaw n

theorem inner (n j : Nat) : run0 table (11+6*n) (middle (n+1) j) = some (middle n (j+1)) := by
  simpa only [middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using innerRaw n j

theorem finish (j : Nat) : run0 table (12+1*j) (middle 0 j) = some (family (j+1)) := by
  simpa only [family,middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append,Nat.one_mul,Nat.zero_mul,Nat.add_zero] using finishRaw j

def cost := epochCost 11 6 11 6 12 1
theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) :=
  growthAll table family middle 11 6 11 6 12 1 first inner finish n


theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 cost entry (by intro n; unfold cost epochCost; omega) growth m hm
#print axioms never

#print axioms growth
end M9651

namespace M9668

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

theorem firstStep0 (n : Nat) : run0 table 2 ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n)), []⟩ = some ⟨0, ([true,true,true]) ++ ((rep [true,true] n)), ([false,true])⟩ := by rfl

theorem firstLocal1 (L R : List Bool) : run0 table 6 ⟨0, ([true,true,true]) ++ (([true,true]) ++ ((L))), (R)⟩ = some ⟨0, ([true,true,true]) ++ ((L)), ([true,true]) ++ ((R))⟩ := by rfl

theorem firstStep1 (n : Nat) : run0 table (6*n) ⟨0, ([true,true,true]) ++ ((rep [true,true] n)), ([false,true])⟩ = some ⟨0, ([true,true,true]), (rep [true,true] n) ++ (([false,true]))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 0 [true,true,true] [] [true,true] [true,true] 6 firstLocal1 n ([]) (([false,true]))

theorem firstStep2 (n : Nat) : run0 table 10 ⟨0, ([true,true,true]), (rep [true,true] n) ++ (([false,true]))⟩ = some ⟨4, ([true,true,false,true]), (rep [true,true] n) ++ (([false,true]))⟩ := by rfl

theorem firstLocal3 (L R : List Bool) : run0 table 2 ⟨4, ([true]) ++ ((L)), ([true,true]) ++ ((R))⟩ = some ⟨4, ([true]) ++ (([true,true]) ++ ((L))), (R)⟩ := by rfl

theorem firstStep3 (n : Nat) : run0 table (2*n) ⟨4, ([true,true,false,true]), (rep [true,true] n) ++ (([false,true]))⟩ = some ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([false,true])⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [] [true,true] [true,true] 2 firstLocal3 n (([true,false,true])) (([false,true]))

theorem firstStep4 (n : Nat) : run0 table 1 ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([false,true])⟩ = some ⟨4, ([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([true])⟩ := by rfl

theorem firstEqL (n : Nat) : (([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true])))) = (([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true])))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 1 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 true) ++ ((List.replicate 1 false) ++ ((List.replicate 1 true))))))) = ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 false) ++ ((List.replicate 1 true))))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem firstRaw (n : Nat) : run0 table (13+8*n) ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n)), []⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true]))), ([true])⟩ := by

  have H := firstStep0 n

  have H := join0 H (firstStep1 n)

  have H := join0 H (firstStep2 n)

  have H := join0 H (firstStep3 n)

  have H := join0 H (firstStep4 n)

  rw [show 2+6*n+10+2*n+1 = 13+8*n by omega] at H

  rw [firstEqL n] at H

  exact H

theorem innerStep0 (n j : Nat) : run0 table 2 ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true]) ++ ((rep [true] j))⟩ = some ⟨0, ([true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem innerLocal1 (L R : List Bool) : run0 table 6 ⟨0, ([true,true,true]) ++ (([true,true]) ++ ((L))), (R)⟩ = some ⟨0, ([true,true,true]) ++ ((L)), ([true,true]) ++ ((R))⟩ := by rfl

theorem innerStep1 (n j : Nat) : run0 table (6*n) ⟨0, ([true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ = some ⟨0, ([true,true,true,false,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 0 [true,true,true] [] [true,true] [true,true] 6 innerLocal1 n (([false,true]) ++ ((rep [true] j))) (([false,true,true]) ++ ((rep [true] j)))

theorem innerStep2 (n j : Nat) : run0 table 10 ⟨0, ([true,true,true,false,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ = some ⟨4, ([true,true,false,true,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ := by rfl

theorem innerLocal3 (L R : List Bool) : run0 table 2 ⟨4, ([true]) ++ ((L)), ([true,true]) ++ ((R))⟩ = some ⟨4, ([true]) ++ (([true,true]) ++ ((L))), (R)⟩ := by rfl

theorem innerStep3 (n j : Nat) : run0 table (2*n) ⟨4, ([true,true,false,true,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ = some ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [] [true,true] [true,true] 2 innerLocal3 n (([true,false,true,true]) ++ ((rep [true] j))) (([false,true,true]) ++ ((rep [true] j)))

theorem innerStep4 (n j : Nat) : run0 table 1 ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem innerEqL (n j : Nat) : (([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j))))) = (([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j))))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 1 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 true) ++ ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 1 true) j)))))))) = ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 1 true) j)))))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem innerRaw (n j : Nat) : run0 table (13+8*n) ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))), ([true,true]) ++ ((rep [true] j))⟩ := by

  have H := innerStep0 n j

  have H := join0 H (innerStep1 n j)

  have H := join0 H (innerStep2 n j)

  have H := join0 H (innerStep3 n j)

  have H := join0 H (innerStep4 n j)

  rw [show 2+6*n+10+2*n+1 = 13+8*n by omega] at H

  rw [innerEqL n j] at H

  exact H

theorem finishStep0 (j : Nat) : run0 table 8 ⟨4, ([false,true,true,false,true]) ++ ((rep [true] j)), ([true]) ++ ((rep [true] j))⟩ = some ⟨4, ([true,true,true]) ++ ((rep [true] j)), ([true,true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem finishLocal1 (L R : List Bool) : run0 table 1 ⟨4, ([true]) ++ ((L)), ([true,true,true]) ++ (([true]) ++ ((R)))⟩ = some ⟨4, ([true]) ++ (([true]) ++ ((L))), ([true,true,true]) ++ ((R))⟩ := by rfl

theorem finishStep1 (j : Nat) : run0 table (1*j) ⟨4, ([true,true,true]) ++ ((rep [true] j)), ([true,true,true]) ++ ((rep [true] j))⟩ = some ⟨4, ([true]) ++ ((rep [true] j) ++ (([true,true]) ++ ((rep [true] j)))), ([true,true,true])⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [true,true,true] [true] [true] 1 finishLocal1 j (([true,true]) ++ ((rep [true] j))) ([])

theorem finishStep2 (j : Nat) : run0 table 4 ⟨4, ([true]) ++ ((rep [true] j) ++ (([true,true]) ++ ((rep [true] j)))), ([true,true,true])⟩ = some ⟨4, ([false,true,true,true,true]) ++ ((rep [true] j) ++ (([true,true]) ++ ((rep [true] j)))), []⟩ := by rfl

theorem finishEqL (j : Nat) : (([false,true,true,true,true]) ++ ((rep [true] j) ++ (([true,true]) ++ ((rep [true] j))))) = (([false,true,true,true,true,true,true]) ++ ((rep [true,true] j))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 4 true) ++ ((rep (List.replicate 1 true) j) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 1 true) j)))))) = ((List.replicate 1 false) ++ ((List.replicate 6 true) ++ ((rep (List.replicate 2 true) j))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem finishRaw (j : Nat) : run0 table (12+1*j) ⟨4, ([false,true,true,false,true]) ++ ((rep [true] j)), ([true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true,true,true,true,true,true]) ++ ((rep [true,true] j)), []⟩ := by

  have H := finishStep0 j

  have H := join0 H (finishStep1 j)

  have H := join0 H (finishStep2 j)

  rw [show 8+1*j+4 = 12+1*j by omega] at H

  rw [finishEqL j] at H

  exact H

abbrev P := [true,true]
abbrev U := [true]
def family (n : Nat) : Z0 := ⟨4,false::rep P (n+2),[]⟩
def middle (n j : Nat) : Z0 := ⟨4,false::(rep P (n+1)++false::rep U (j+1)),rep U (j+1)⟩


theorem first (n : Nat) : run0 table (13+8*n) (family n) = some (middle n 0) := by
  simpa only [family,middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using firstRaw n

theorem inner (n j : Nat) : run0 table (13+8*n) (middle (n+1) j) = some (middle n (j+1)) := by
  simpa only [middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using innerRaw n j

theorem finish (j : Nat) : run0 table (12+1*j) (middle 0 j) = some (family (j+1)) := by
  simpa only [family,middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append,Nat.one_mul,Nat.zero_mul,Nat.add_zero] using finishRaw j

def cost := epochCost 13 8 13 8 12 1
theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) :=
  growthAll table family middle 13 8 13 8 12 1 first inner finish n


theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 cost entry (by intro n; unfold cost epochCost; omega) growth m hm
#print axioms never

#print axioms growth
end M9668
end BB6.Agent11Raw121QuadraticExtra
