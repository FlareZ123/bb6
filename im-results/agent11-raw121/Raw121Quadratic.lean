import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw121Quadratic
open BB6Coverage BB6Coverage.Agent31Pump

theorem repReplicate (b : Bool) (k n : Nat) :
    rep (List.replicate k b) n = List.replicate (k*n) b := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep,ih,List.replicate_append_replicate,show k+k*n=k*(n+1) by rw [Nat.mul_succ,Nat.add_comm]]

theorem replicateAddTail (b : Bool) (a c : Nat) (R : List Bool) :
    List.replicate a b ++ (List.replicate c b ++ R) = List.replicate (a+c) b ++ R := by
  rw [← List.append_assoc,List.replicate_append_replicate]

abbrev P := [true,true]
abbrev U := [true]
def family (n : Nat) : Z0 := ⟨4,false::rep P (n+2),[]⟩
def middle (n j : Nat) : Z0 := ⟨4,false::(rep P (n+1)++false::rep U (j+1)),rep U (j+1)⟩
def innerCost (a : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => a+4*n+innerCost a n

theorem innerAll (p : PartialMachine) (a : Nat)
    (one : ∀ n j, run0 p (a+4*n) (middle (n+1) j) = some (middle n (j+1)))
    (n j : Nat) : run0 p (innerCost a n) (middle n j) = some (middle 0 (j+n)) := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    have H := join0 (one n j) (ih (j+1))
    simpa only [innerCost,show j+1+n=j+(n+1) by omega] using H

def cost (a b c n : Nat) := a+4*n+innerCost b n+(c+n)
theorem growthAll (p : PartialMachine) (a b c : Nat)
    (first : ∀ n, run0 p (a+4*n) (family n) = some (middle n 0))
    (one : ∀ n j, run0 p (b+4*n) (middle (n+1) j) = some (middle n (j+1)))
    (last : ∀ j, run0 p (c+j) (middle 0 j) = some (family (j+1)))
    (n : Nat) : run0 p (cost a b c n) (family n) = some (family (n+1)) := by
  have H := join0 (first n) (innerAll p b one n 0)
  rw [Nat.zero_add] at H
  exact join0 H (last n)


namespace M4410

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

theorem firstStep0 (n : Nat) : run0 table 2 ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n)), []⟩ = some ⟨1, ([true,true,true]) ++ ((rep [true,true] n)), ([false,true])⟩ := by rfl

theorem firstLocal1 (L R : List Bool) : run0 table 2 ⟨1, ([true,true,true]) ++ (([true,true]) ++ ((L))), (R)⟩ = some ⟨1, ([true,true,true]) ++ ((L)), ([true,true]) ++ ((R))⟩ := by rfl

theorem firstStep1 (n : Nat) : run0 table (2*n) ⟨1, ([true,true,true]) ++ ((rep [true,true] n)), ([false,true])⟩ = some ⟨1, ([true,true,true]), (rep [true,true] n) ++ (([false,true]))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 1 [true,true,true] [] [true,true] [true,true] 2 firstLocal1 n ([]) (([false,true]))

theorem firstStep2 (n : Nat) : run0 table 8 ⟨1, ([true,true,true]), (rep [true,true] n) ++ (([false,true]))⟩ = some ⟨4, ([true,true,false,true]), (rep [true,true] n) ++ (([false,true]))⟩ := by rfl

theorem firstLocal3 (L R : List Bool) : run0 table 2 ⟨4, ([true]) ++ ((L)), ([true,true]) ++ ((R))⟩ = some ⟨4, ([true]) ++ (([true,true]) ++ ((L))), (R)⟩ := by rfl

theorem firstStep3 (n : Nat) : run0 table (2*n) ⟨4, ([true,true,false,true]), (rep [true,true] n) ++ (([false,true]))⟩ = some ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([false,true])⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [] [true,true] [true,true] 2 firstLocal3 n (([true,false,true])) (([false,true]))

theorem firstStep4 (n : Nat) : run0 table 1 ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([false,true])⟩ = some ⟨4, ([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([true])⟩ := by rfl

theorem firstEqL (n : Nat) : (([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true])))) = (([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true])))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 1 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 true) ++ ((List.replicate 1 false) ++ ((List.replicate 1 true))))))) = ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 false) ++ ((List.replicate 1 true))))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem firstRaw (n : Nat) : run0 table (11+4*n) ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n)), []⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true]))), ([true])⟩ := by

  have H := firstStep0 n

  have H := join0 H (firstStep1 n)

  have H := join0 H (firstStep2 n)

  have H := join0 H (firstStep3 n)

  have H := join0 H (firstStep4 n)

  rw [show 2+2*n+8+2*n+1 = 11+4*n by omega] at H

  rw [firstEqL n] at H

  exact H

theorem innerStep0 (n j : Nat) : run0 table 2 ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true]) ++ ((rep [true] j))⟩ = some ⟨1, ([true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem innerLocal1 (L R : List Bool) : run0 table 2 ⟨1, ([true,true,true]) ++ (([true,true]) ++ ((L))), (R)⟩ = some ⟨1, ([true,true,true]) ++ ((L)), ([true,true]) ++ ((R))⟩ := by rfl

theorem innerStep1 (n j : Nat) : run0 table (2*n) ⟨1, ([true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ = some ⟨1, ([true,true,true,false,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 1 [true,true,true] [] [true,true] [true,true] 2 innerLocal1 n (([false,true]) ++ ((rep [true] j))) (([false,true,true]) ++ ((rep [true] j)))

theorem innerStep2 (n j : Nat) : run0 table 8 ⟨1, ([true,true,true,false,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ = some ⟨4, ([true,true,false,true,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ := by rfl

theorem innerLocal3 (L R : List Bool) : run0 table 2 ⟨4, ([true]) ++ ((L)), ([true,true]) ++ ((R))⟩ = some ⟨4, ([true]) ++ (([true,true]) ++ ((L))), (R)⟩ := by rfl

theorem innerStep3 (n j : Nat) : run0 table (2*n) ⟨4, ([true,true,false,true,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ = some ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [] [true,true] [true,true] 2 innerLocal3 n (([true,false,true,true]) ++ ((rep [true] j))) (([false,true,true]) ++ ((rep [true] j)))

theorem innerStep4 (n j : Nat) : run0 table 1 ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem innerEqL (n j : Nat) : (([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j))))) = (([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j))))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 1 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 true) ++ ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 1 true) j)))))))) = ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 1 true) j)))))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem innerRaw (n j : Nat) : run0 table (11+4*n) ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))), ([true,true]) ++ ((rep [true] j))⟩ := by

  have H := innerStep0 n j

  have H := join0 H (innerStep1 n j)

  have H := join0 H (innerStep2 n j)

  have H := join0 H (innerStep3 n j)

  have H := join0 H (innerStep4 n j)

  rw [show 2+2*n+8+2*n+1 = 11+4*n by omega] at H

  rw [innerEqL n j] at H

  exact H

theorem finishStep0 (j : Nat) : run0 table 10 ⟨4, ([false,true,true,false,true]) ++ ((rep [true] j)), ([true]) ++ ((rep [true] j))⟩ = some ⟨4, ([true,true,true]) ++ ((rep [true] j)), ([true,true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem finishLocal1 (L R : List Bool) : run0 table 1 ⟨4, ([true]) ++ ((L)), ([true,true,true]) ++ (([true]) ++ ((R)))⟩ = some ⟨4, ([true]) ++ (([true]) ++ ((L))), ([true,true,true]) ++ ((R))⟩ := by rfl

theorem finishStep1 (j : Nat) : run0 table (1*j) ⟨4, ([true,true,true]) ++ ((rep [true] j)), ([true,true,true]) ++ ((rep [true] j))⟩ = some ⟨4, ([true]) ++ ((rep [true] j) ++ (([true,true]) ++ ((rep [true] j)))), ([true,true,true])⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [true,true,true] [true] [true] 1 finishLocal1 j (([true,true]) ++ ((rep [true] j))) ([])

theorem finishStep2 (j : Nat) : run0 table 4 ⟨4, ([true]) ++ ((rep [true] j) ++ (([true,true]) ++ ((rep [true] j)))), ([true,true,true])⟩ = some ⟨4, ([false,true,true,true,true]) ++ ((rep [true] j) ++ (([true,true]) ++ ((rep [true] j)))), []⟩ := by rfl

theorem finishEqL (j : Nat) : (([false,true,true,true,true]) ++ ((rep [true] j) ++ (([true,true]) ++ ((rep [true] j))))) = (([false,true,true,true,true,true,true]) ++ ((rep [true,true] j))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 4 true) ++ ((rep (List.replicate 1 true) j) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 1 true) j)))))) = ((List.replicate 1 false) ++ ((List.replicate 6 true) ++ ((rep (List.replicate 2 true) j))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem finishRaw (j : Nat) : run0 table (14+1*j) ⟨4, ([false,true,true,false,true]) ++ ((rep [true] j)), ([true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true,true,true,true,true,true]) ++ ((rep [true,true] j)), []⟩ := by

  have H := finishStep0 j

  have H := join0 H (finishStep1 j)

  have H := join0 H (finishStep2 j)

  rw [show 10+1*j+4 = 14+1*j by omega] at H

  rw [finishEqL j] at H

  exact H

theorem first (n : Nat) : run0 table (11+4*n) (family n) = some (middle n 0) := by
  simpa only [family,middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using firstRaw n

theorem inner (n j : Nat) : run0 table (11+4*n) (middle (n+1) j) = some (middle n (j+1)) := by
  simpa only [middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using innerRaw n j

theorem finish (j : Nat) : run0 table (14+j) (middle 0 j) = some (family (j+1)) := by
  simpa only [family,middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append,Nat.one_mul] using finishRaw j

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (cost 11 11 14 n) (family n) = some (family (n+1)) :=
  growthAll table 11 11 14 first inner finish n


theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (cost 11 11 14) entry (by intro n; unfold cost; omega) growth m hm
#print axioms never

#print axioms growth
end M4410

namespace M4799

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

theorem firstStep0 (n : Nat) : run0 table 3 ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n)), []⟩ = some ⟨1, ([true,true]) ++ ((rep [true,true] n)), ([true,false,true])⟩ := by rfl

theorem firstLocal1 (L R : List Bool) : run0 table 2 ⟨1, ([true,true]) ++ (([true,true]) ++ ((L))), ([true]) ++ ((R))⟩ = some ⟨1, ([true,true]) ++ ((L)), ([true]) ++ (([true,true]) ++ ((R)))⟩ := by rfl

theorem firstStep1 (n : Nat) : run0 table (2*n) ⟨1, ([true,true]) ++ ((rep [true,true] n)), ([true,false,true])⟩ = some ⟨1, ([true,true]), ([true]) ++ ((rep [true,true] n) ++ (([false,true])))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 1 [true,true] [true] [true,true] [true,true] 2 firstLocal1 n ([]) (([false,true]))

theorem firstStep2 (n : Nat) : run0 table 5 ⟨1, ([true,true]), ([true]) ++ ((rep [true,true] n) ++ (([false,true])))⟩ = some ⟨4, ([true,true,false,true]), (rep [true,true] n) ++ (([false,true]))⟩ := by rfl

theorem firstLocal3 (L R : List Bool) : run0 table 2 ⟨4, ([true]) ++ ((L)), ([true,true]) ++ ((R))⟩ = some ⟨4, ([true]) ++ (([true,true]) ++ ((L))), (R)⟩ := by rfl

theorem firstStep3 (n : Nat) : run0 table (2*n) ⟨4, ([true,true,false,true]), (rep [true,true] n) ++ (([false,true]))⟩ = some ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([false,true])⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [] [true,true] [true,true] 2 firstLocal3 n (([true,false,true])) (([false,true]))

theorem firstStep4 (n : Nat) : run0 table 1 ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([false,true])⟩ = some ⟨4, ([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([true])⟩ := by rfl

theorem firstEqL (n : Nat) : (([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true])))) = (([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true])))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 1 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 true) ++ ((List.replicate 1 false) ++ ((List.replicate 1 true))))))) = ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 false) ++ ((List.replicate 1 true))))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem firstRaw (n : Nat) : run0 table (9+4*n) ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n)), []⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true]))), ([true])⟩ := by

  have H := firstStep0 n

  have H := join0 H (firstStep1 n)

  have H := join0 H (firstStep2 n)

  have H := join0 H (firstStep3 n)

  have H := join0 H (firstStep4 n)

  rw [show 3+2*n+5+2*n+1 = 9+4*n by omega] at H

  rw [firstEqL n] at H

  exact H

theorem innerStep0 (n j : Nat) : run0 table 3 ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true]) ++ ((rep [true] j))⟩ = some ⟨1, ([true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true,false,true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem innerLocal1 (L R : List Bool) : run0 table 2 ⟨1, ([true,true]) ++ (([true,true]) ++ ((L))), ([true]) ++ ((R))⟩ = some ⟨1, ([true,true]) ++ ((L)), ([true]) ++ (([true,true]) ++ ((R)))⟩ := by rfl

theorem innerStep1 (n j : Nat) : run0 table (2*n) ⟨1, ([true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true,false,true,true]) ++ ((rep [true] j))⟩ = some ⟨1, ([true,true,false,true]) ++ ((rep [true] j)), ([true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j))))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 1 [true,true] [true] [true,true] [true,true] 2 innerLocal1 n (([false,true]) ++ ((rep [true] j))) (([false,true,true]) ++ ((rep [true] j)))

theorem innerStep2 (n j : Nat) : run0 table 5 ⟨1, ([true,true,false,true]) ++ ((rep [true] j)), ([true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j))))⟩ = some ⟨4, ([true,true,false,true,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ := by rfl

theorem innerLocal3 (L R : List Bool) : run0 table 2 ⟨4, ([true]) ++ ((L)), ([true,true]) ++ ((R))⟩ = some ⟨4, ([true]) ++ (([true,true]) ++ ((L))), (R)⟩ := by rfl

theorem innerStep3 (n j : Nat) : run0 table (2*n) ⟨4, ([true,true,false,true,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ = some ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [] [true,true] [true,true] 2 innerLocal3 n (([true,false,true,true]) ++ ((rep [true] j))) (([false,true,true]) ++ ((rep [true] j)))

theorem innerStep4 (n j : Nat) : run0 table 1 ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem innerEqL (n j : Nat) : (([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j))))) = (([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j))))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 1 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 true) ++ ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 1 true) j)))))))) = ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 1 true) j)))))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem innerRaw (n j : Nat) : run0 table (9+4*n) ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))), ([true,true]) ++ ((rep [true] j))⟩ := by

  have H := innerStep0 n j

  have H := join0 H (innerStep1 n j)

  have H := join0 H (innerStep2 n j)

  have H := join0 H (innerStep3 n j)

  have H := join0 H (innerStep4 n j)

  rw [show 3+2*n+5+2*n+1 = 9+4*n by omega] at H

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

theorem first (n : Nat) : run0 table (9+4*n) (family n) = some (middle n 0) := by
  simpa only [family,middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using firstRaw n

theorem inner (n j : Nat) : run0 table (9+4*n) (middle (n+1) j) = some (middle n (j+1)) := by
  simpa only [middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using innerRaw n j

theorem finish (j : Nat) : run0 table (12+j) (middle 0 j) = some (family (j+1)) := by
  simpa only [family,middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append,Nat.one_mul] using finishRaw j

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (cost 9 9 12 n) (family n) = some (family (n+1)) :=
  growthAll table 9 9 12 first inner finish n


theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (cost 9 9 12) entry (by intro n; unfold cost; omega) growth m hm
#print axioms never

#print axioms growth
end M4799

namespace M4801

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

theorem firstStep0 (n : Nat) : run0 table 2 ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n)), []⟩ = some ⟨5, ([true,true,true]) ++ ((rep [true,true] n)), ([false,true])⟩ := by rfl

theorem firstLocal1 (L R : List Bool) : run0 table 2 ⟨5, ([true,true,true]) ++ (([true,true]) ++ ((L))), (R)⟩ = some ⟨5, ([true,true,true]) ++ ((L)), ([true,true]) ++ ((R))⟩ := by rfl

theorem firstStep1 (n : Nat) : run0 table (2*n) ⟨5, ([true,true,true]) ++ ((rep [true,true] n)), ([false,true])⟩ = some ⟨5, ([true,true,true]), (rep [true,true] n) ++ (([false,true]))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 5 [true,true,true] [] [true,true] [true,true] 2 firstLocal1 n ([]) (([false,true]))

theorem firstStep2 (n : Nat) : run0 table 6 ⟨5, ([true,true,true]), (rep [true,true] n) ++ (([false,true]))⟩ = some ⟨4, ([true,true,false,true]), (rep [true,true] n) ++ (([false,true]))⟩ := by rfl

theorem firstLocal3 (L R : List Bool) : run0 table 2 ⟨4, ([true]) ++ ((L)), ([true,true]) ++ ((R))⟩ = some ⟨4, ([true]) ++ (([true,true]) ++ ((L))), (R)⟩ := by rfl

theorem firstStep3 (n : Nat) : run0 table (2*n) ⟨4, ([true,true,false,true]), (rep [true,true] n) ++ (([false,true]))⟩ = some ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([false,true])⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [] [true,true] [true,true] 2 firstLocal3 n (([true,false,true])) (([false,true]))

theorem firstStep4 (n : Nat) : run0 table 1 ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([false,true])⟩ = some ⟨4, ([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([true])⟩ := by rfl

theorem firstEqL (n : Nat) : (([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true])))) = (([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true])))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 1 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 true) ++ ((List.replicate 1 false) ++ ((List.replicate 1 true))))))) = ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 false) ++ ((List.replicate 1 true))))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem firstRaw (n : Nat) : run0 table (9+4*n) ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n)), []⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true]))), ([true])⟩ := by

  have H := firstStep0 n

  have H := join0 H (firstStep1 n)

  have H := join0 H (firstStep2 n)

  have H := join0 H (firstStep3 n)

  have H := join0 H (firstStep4 n)

  rw [show 2+2*n+6+2*n+1 = 9+4*n by omega] at H

  rw [firstEqL n] at H

  exact H

theorem innerStep0 (n j : Nat) : run0 table 2 ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true]) ++ ((rep [true] j))⟩ = some ⟨5, ([true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem innerLocal1 (L R : List Bool) : run0 table 2 ⟨5, ([true,true,true]) ++ (([true,true]) ++ ((L))), (R)⟩ = some ⟨5, ([true,true,true]) ++ ((L)), ([true,true]) ++ ((R))⟩ := by rfl

theorem innerStep1 (n j : Nat) : run0 table (2*n) ⟨5, ([true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ = some ⟨5, ([true,true,true,false,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 5 [true,true,true] [] [true,true] [true,true] 2 innerLocal1 n (([false,true]) ++ ((rep [true] j))) (([false,true,true]) ++ ((rep [true] j)))

theorem innerStep2 (n j : Nat) : run0 table 6 ⟨5, ([true,true,true,false,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ = some ⟨4, ([true,true,false,true,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ := by rfl

theorem innerLocal3 (L R : List Bool) : run0 table 2 ⟨4, ([true]) ++ ((L)), ([true,true]) ++ ((R))⟩ = some ⟨4, ([true]) ++ (([true,true]) ++ ((L))), (R)⟩ := by rfl

theorem innerStep3 (n j : Nat) : run0 table (2*n) ⟨4, ([true,true,false,true,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ = some ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [] [true,true] [true,true] 2 innerLocal3 n (([true,false,true,true]) ++ ((rep [true] j))) (([false,true,true]) ++ ((rep [true] j)))

theorem innerStep4 (n j : Nat) : run0 table 1 ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem innerEqL (n j : Nat) : (([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j))))) = (([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j))))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 1 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 true) ++ ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 1 true) j)))))))) = ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 1 true) j)))))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem innerRaw (n j : Nat) : run0 table (9+4*n) ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))), ([true,true]) ++ ((rep [true] j))⟩ := by

  have H := innerStep0 n j

  have H := join0 H (innerStep1 n j)

  have H := join0 H (innerStep2 n j)

  have H := join0 H (innerStep3 n j)

  have H := join0 H (innerStep4 n j)

  rw [show 2+2*n+6+2*n+1 = 9+4*n by omega] at H

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

theorem first (n : Nat) : run0 table (9+4*n) (family n) = some (middle n 0) := by
  simpa only [family,middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using firstRaw n

theorem inner (n j : Nat) : run0 table (9+4*n) (middle (n+1) j) = some (middle n (j+1)) := by
  simpa only [middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using innerRaw n j

theorem finish (j : Nat) : run0 table (12+j) (middle 0 j) = some (family (j+1)) := by
  simpa only [family,middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append,Nat.one_mul] using finishRaw j

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (cost 9 9 12 n) (family n) = some (family (n+1)) :=
  growthAll table 9 9 12 first inner finish n


theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (cost 9 9 12) entry (by intro n; unfold cost; omega) growth m hm
#print axioms never

#print axioms growth
end M4801

namespace M4882

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

theorem firstStep0 (n : Nat) : run0 table 2 ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n)), []⟩ = some ⟨5, ([true,true,true]) ++ ((rep [true,true] n)), ([false,true])⟩ := by rfl

theorem firstLocal1 (L R : List Bool) : run0 table 2 ⟨5, ([true,true,true]) ++ (([true,true]) ++ ((L))), (R)⟩ = some ⟨5, ([true,true,true]) ++ ((L)), ([true,true]) ++ ((R))⟩ := by rfl

theorem firstStep1 (n : Nat) : run0 table (2*n) ⟨5, ([true,true,true]) ++ ((rep [true,true] n)), ([false,true])⟩ = some ⟨5, ([true,true,true]), (rep [true,true] n) ++ (([false,true]))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 5 [true,true,true] [] [true,true] [true,true] 2 firstLocal1 n ([]) (([false,true]))

theorem firstStep2 (n : Nat) : run0 table 8 ⟨5, ([true,true,true]), (rep [true,true] n) ++ (([false,true]))⟩ = some ⟨4, ([true,true,false,true]), (rep [true,true] n) ++ (([false,true]))⟩ := by rfl

theorem firstLocal3 (L R : List Bool) : run0 table 2 ⟨4, ([true]) ++ ((L)), ([true,true]) ++ ((R))⟩ = some ⟨4, ([true]) ++ (([true,true]) ++ ((L))), (R)⟩ := by rfl

theorem firstStep3 (n : Nat) : run0 table (2*n) ⟨4, ([true,true,false,true]), (rep [true,true] n) ++ (([false,true]))⟩ = some ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([false,true])⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [] [true,true] [true,true] 2 firstLocal3 n (([true,false,true])) (([false,true]))

theorem firstStep4 (n : Nat) : run0 table 1 ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([false,true])⟩ = some ⟨4, ([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([true])⟩ := by rfl

theorem firstEqL (n : Nat) : (([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true])))) = (([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true])))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 1 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 true) ++ ((List.replicate 1 false) ++ ((List.replicate 1 true))))))) = ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 false) ++ ((List.replicate 1 true))))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem firstRaw (n : Nat) : run0 table (11+4*n) ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n)), []⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true]))), ([true])⟩ := by

  have H := firstStep0 n

  have H := join0 H (firstStep1 n)

  have H := join0 H (firstStep2 n)

  have H := join0 H (firstStep3 n)

  have H := join0 H (firstStep4 n)

  rw [show 2+2*n+8+2*n+1 = 11+4*n by omega] at H

  rw [firstEqL n] at H

  exact H

theorem innerStep0 (n j : Nat) : run0 table 2 ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true]) ++ ((rep [true] j))⟩ = some ⟨5, ([true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem innerLocal1 (L R : List Bool) : run0 table 2 ⟨5, ([true,true,true]) ++ (([true,true]) ++ ((L))), (R)⟩ = some ⟨5, ([true,true,true]) ++ ((L)), ([true,true]) ++ ((R))⟩ := by rfl

theorem innerStep1 (n j : Nat) : run0 table (2*n) ⟨5, ([true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ = some ⟨5, ([true,true,true,false,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 5 [true,true,true] [] [true,true] [true,true] 2 innerLocal1 n (([false,true]) ++ ((rep [true] j))) (([false,true,true]) ++ ((rep [true] j)))

theorem innerStep2 (n j : Nat) : run0 table 8 ⟨5, ([true,true,true,false,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ = some ⟨4, ([true,true,false,true,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ := by rfl

theorem innerLocal3 (L R : List Bool) : run0 table 2 ⟨4, ([true]) ++ ((L)), ([true,true]) ++ ((R))⟩ = some ⟨4, ([true]) ++ (([true,true]) ++ ((L))), (R)⟩ := by rfl

theorem innerStep3 (n j : Nat) : run0 table (2*n) ⟨4, ([true,true,false,true,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ = some ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [] [true,true] [true,true] 2 innerLocal3 n (([true,false,true,true]) ++ ((rep [true] j))) (([false,true,true]) ++ ((rep [true] j)))

theorem innerStep4 (n j : Nat) : run0 table 1 ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem innerEqL (n j : Nat) : (([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j))))) = (([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j))))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 1 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 true) ++ ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 1 true) j)))))))) = ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 1 true) j)))))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem innerRaw (n j : Nat) : run0 table (11+4*n) ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))), ([true,true]) ++ ((rep [true] j))⟩ := by

  have H := innerStep0 n j

  have H := join0 H (innerStep1 n j)

  have H := join0 H (innerStep2 n j)

  have H := join0 H (innerStep3 n j)

  have H := join0 H (innerStep4 n j)

  rw [show 2+2*n+8+2*n+1 = 11+4*n by omega] at H

  rw [innerEqL n j] at H

  exact H

theorem finishStep0 (j : Nat) : run0 table 10 ⟨4, ([false,true,true,false,true]) ++ ((rep [true] j)), ([true]) ++ ((rep [true] j))⟩ = some ⟨4, ([true,true,true]) ++ ((rep [true] j)), ([true,true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem finishLocal1 (L R : List Bool) : run0 table 1 ⟨4, ([true]) ++ ((L)), ([true,true,true]) ++ (([true]) ++ ((R)))⟩ = some ⟨4, ([true]) ++ (([true]) ++ ((L))), ([true,true,true]) ++ ((R))⟩ := by rfl

theorem finishStep1 (j : Nat) : run0 table (1*j) ⟨4, ([true,true,true]) ++ ((rep [true] j)), ([true,true,true]) ++ ((rep [true] j))⟩ = some ⟨4, ([true]) ++ ((rep [true] j) ++ (([true,true]) ++ ((rep [true] j)))), ([true,true,true])⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [true,true,true] [true] [true] 1 finishLocal1 j (([true,true]) ++ ((rep [true] j))) ([])

theorem finishStep2 (j : Nat) : run0 table 4 ⟨4, ([true]) ++ ((rep [true] j) ++ (([true,true]) ++ ((rep [true] j)))), ([true,true,true])⟩ = some ⟨4, ([false,true,true,true,true]) ++ ((rep [true] j) ++ (([true,true]) ++ ((rep [true] j)))), []⟩ := by rfl

theorem finishEqL (j : Nat) : (([false,true,true,true,true]) ++ ((rep [true] j) ++ (([true,true]) ++ ((rep [true] j))))) = (([false,true,true,true,true,true,true]) ++ ((rep [true,true] j))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 4 true) ++ ((rep (List.replicate 1 true) j) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 1 true) j)))))) = ((List.replicate 1 false) ++ ((List.replicate 6 true) ++ ((rep (List.replicate 2 true) j))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem finishRaw (j : Nat) : run0 table (14+1*j) ⟨4, ([false,true,true,false,true]) ++ ((rep [true] j)), ([true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true,true,true,true,true,true]) ++ ((rep [true,true] j)), []⟩ := by

  have H := finishStep0 j

  have H := join0 H (finishStep1 j)

  have H := join0 H (finishStep2 j)

  rw [show 10+1*j+4 = 14+1*j by omega] at H

  rw [finishEqL j] at H

  exact H

theorem first (n : Nat) : run0 table (11+4*n) (family n) = some (middle n 0) := by
  simpa only [family,middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using firstRaw n

theorem inner (n j : Nat) : run0 table (11+4*n) (middle (n+1) j) = some (middle n (j+1)) := by
  simpa only [middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using innerRaw n j

theorem finish (j : Nat) : run0 table (14+j) (middle 0 j) = some (family (j+1)) := by
  simpa only [family,middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append,Nat.one_mul] using finishRaw j

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (cost 11 11 14 n) (family n) = some (family (n+1)) :=
  growthAll table 11 11 14 first inner finish n


theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (cost 11 11 14) entry (by intro n; unfold cost; omega) growth m hm
#print axioms never

#print axioms growth
end M4882

namespace M4916

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,true,1⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

theorem firstStep0 (n : Nat) : run0 table 2 ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n)), []⟩ = some ⟨5, ([true,true,true]) ++ ((rep [true,true] n)), ([false,true])⟩ := by rfl

theorem firstLocal1 (L R : List Bool) : run0 table 2 ⟨5, ([true,true,true]) ++ (([true,true]) ++ ((L))), (R)⟩ = some ⟨5, ([true,true,true]) ++ ((L)), ([true,true]) ++ ((R))⟩ := by rfl

theorem firstStep1 (n : Nat) : run0 table (2*n) ⟨5, ([true,true,true]) ++ ((rep [true,true] n)), ([false,true])⟩ = some ⟨5, ([true,true,true]), (rep [true,true] n) ++ (([false,true]))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 5 [true,true,true] [] [true,true] [true,true] 2 firstLocal1 n ([]) (([false,true]))

theorem firstStep2 (n : Nat) : run0 table 6 ⟨5, ([true,true,true]), (rep [true,true] n) ++ (([false,true]))⟩ = some ⟨4, ([true,true,false,true]), (rep [true,true] n) ++ (([false,true]))⟩ := by rfl

theorem firstLocal3 (L R : List Bool) : run0 table 2 ⟨4, ([true]) ++ ((L)), ([true,true]) ++ ((R))⟩ = some ⟨4, ([true]) ++ (([true,true]) ++ ((L))), (R)⟩ := by rfl

theorem firstStep3 (n : Nat) : run0 table (2*n) ⟨4, ([true,true,false,true]), (rep [true,true] n) ++ (([false,true]))⟩ = some ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([false,true])⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [] [true,true] [true,true] 2 firstLocal3 n (([true,false,true])) (([false,true]))

theorem firstStep4 (n : Nat) : run0 table 1 ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([false,true])⟩ = some ⟨4, ([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([true])⟩ := by rfl

theorem firstEqL (n : Nat) : (([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true])))) = (([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true])))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 1 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 true) ++ ((List.replicate 1 false) ++ ((List.replicate 1 true))))))) = ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 false) ++ ((List.replicate 1 true))))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem firstRaw (n : Nat) : run0 table (9+4*n) ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n)), []⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true]))), ([true])⟩ := by

  have H := firstStep0 n

  have H := join0 H (firstStep1 n)

  have H := join0 H (firstStep2 n)

  have H := join0 H (firstStep3 n)

  have H := join0 H (firstStep4 n)

  rw [show 2+2*n+6+2*n+1 = 9+4*n by omega] at H

  rw [firstEqL n] at H

  exact H

theorem innerStep0 (n j : Nat) : run0 table 2 ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true]) ++ ((rep [true] j))⟩ = some ⟨5, ([true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem innerLocal1 (L R : List Bool) : run0 table 2 ⟨5, ([true,true,true]) ++ (([true,true]) ++ ((L))), (R)⟩ = some ⟨5, ([true,true,true]) ++ ((L)), ([true,true]) ++ ((R))⟩ := by rfl

theorem innerStep1 (n j : Nat) : run0 table (2*n) ⟨5, ([true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ = some ⟨5, ([true,true,true,false,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 5 [true,true,true] [] [true,true] [true,true] 2 innerLocal1 n (([false,true]) ++ ((rep [true] j))) (([false,true,true]) ++ ((rep [true] j)))

theorem innerStep2 (n j : Nat) : run0 table 6 ⟨5, ([true,true,true,false,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ = some ⟨4, ([true,true,false,true,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ := by rfl

theorem innerLocal3 (L R : List Bool) : run0 table 2 ⟨4, ([true]) ++ ((L)), ([true,true]) ++ ((R))⟩ = some ⟨4, ([true]) ++ (([true,true]) ++ ((L))), (R)⟩ := by rfl

theorem innerStep3 (n j : Nat) : run0 table (2*n) ⟨4, ([true,true,false,true,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ = some ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [] [true,true] [true,true] 2 innerLocal3 n (([true,false,true,true]) ++ ((rep [true] j))) (([false,true,true]) ++ ((rep [true] j)))

theorem innerStep4 (n j : Nat) : run0 table 1 ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem innerEqL (n j : Nat) : (([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j))))) = (([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j))))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 1 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 true) ++ ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 1 true) j)))))))) = ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 1 true) j)))))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem innerRaw (n j : Nat) : run0 table (9+4*n) ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))), ([true,true]) ++ ((rep [true] j))⟩ := by

  have H := innerStep0 n j

  have H := join0 H (innerStep1 n j)

  have H := join0 H (innerStep2 n j)

  have H := join0 H (innerStep3 n j)

  have H := join0 H (innerStep4 n j)

  rw [show 2+2*n+6+2*n+1 = 9+4*n by omega] at H

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

theorem first (n : Nat) : run0 table (9+4*n) (family n) = some (middle n 0) := by
  simpa only [family,middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using firstRaw n

theorem inner (n j : Nat) : run0 table (9+4*n) (middle (n+1) j) = some (middle n (j+1)) := by
  simpa only [middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using innerRaw n j

theorem finish (j : Nat) : run0 table (12+j) (middle 0 j) = some (family (j+1)) := by
  simpa only [family,middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append,Nat.one_mul] using finishRaw j

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (cost 9 9 12 n) (family n) = some (family (n+1)) :=
  growthAll table 9 9 12 first inner finish n


theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (cost 9 9 12) entry (by intro n; unfold cost; omega) growth m hm
#print axioms never

#print axioms growth
end M4916

namespace M8749

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none

theorem firstStep0 (n : Nat) : run0 table 3 ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n)), []⟩ = some ⟨0, ([true,true]) ++ ((rep [true,true] n)), ([true,false,true])⟩ := by rfl

theorem firstLocal1 (L R : List Bool) : run0 table 2 ⟨0, ([true,true]) ++ (([true,true]) ++ ((L))), ([true]) ++ ((R))⟩ = some ⟨0, ([true,true]) ++ ((L)), ([true]) ++ (([true,true]) ++ ((R)))⟩ := by rfl

theorem firstStep1 (n : Nat) : run0 table (2*n) ⟨0, ([true,true]) ++ ((rep [true,true] n)), ([true,false,true])⟩ = some ⟨0, ([true,true]), ([true]) ++ ((rep [true,true] n) ++ (([false,true])))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 0 [true,true] [true] [true,true] [true,true] 2 firstLocal1 n ([]) (([false,true]))

theorem firstStep2 (n : Nat) : run0 table 5 ⟨0, ([true,true]), ([true]) ++ ((rep [true,true] n) ++ (([false,true])))⟩ = some ⟨4, ([true,true,false,true]), (rep [true,true] n) ++ (([false,true]))⟩ := by rfl

theorem firstLocal3 (L R : List Bool) : run0 table 2 ⟨4, ([true]) ++ ((L)), ([true,true]) ++ ((R))⟩ = some ⟨4, ([true]) ++ (([true,true]) ++ ((L))), (R)⟩ := by rfl

theorem firstStep3 (n : Nat) : run0 table (2*n) ⟨4, ([true,true,false,true]), (rep [true,true] n) ++ (([false,true]))⟩ = some ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([false,true])⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [] [true,true] [true,true] 2 firstLocal3 n (([true,false,true])) (([false,true]))

theorem firstStep4 (n : Nat) : run0 table 1 ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([false,true])⟩ = some ⟨4, ([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([true])⟩ := by rfl

theorem firstEqL (n : Nat) : (([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true])))) = (([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true])))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 1 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 true) ++ ((List.replicate 1 false) ++ ((List.replicate 1 true))))))) = ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 false) ++ ((List.replicate 1 true))))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem firstRaw (n : Nat) : run0 table (9+4*n) ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n)), []⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true]))), ([true])⟩ := by

  have H := firstStep0 n

  have H := join0 H (firstStep1 n)

  have H := join0 H (firstStep2 n)

  have H := join0 H (firstStep3 n)

  have H := join0 H (firstStep4 n)

  rw [show 3+2*n+5+2*n+1 = 9+4*n by omega] at H

  rw [firstEqL n] at H

  exact H

theorem innerStep0 (n j : Nat) : run0 table 3 ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true]) ++ ((rep [true] j))⟩ = some ⟨0, ([true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true,false,true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem innerLocal1 (L R : List Bool) : run0 table 2 ⟨0, ([true,true]) ++ (([true,true]) ++ ((L))), ([true]) ++ ((R))⟩ = some ⟨0, ([true,true]) ++ ((L)), ([true]) ++ (([true,true]) ++ ((R)))⟩ := by rfl

theorem innerStep1 (n j : Nat) : run0 table (2*n) ⟨0, ([true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true,false,true,true]) ++ ((rep [true] j))⟩ = some ⟨0, ([true,true,false,true]) ++ ((rep [true] j)), ([true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j))))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 0 [true,true] [true] [true,true] [true,true] 2 innerLocal1 n (([false,true]) ++ ((rep [true] j))) (([false,true,true]) ++ ((rep [true] j)))

theorem innerStep2 (n j : Nat) : run0 table 5 ⟨0, ([true,true,false,true]) ++ ((rep [true] j)), ([true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j))))⟩ = some ⟨4, ([true,true,false,true,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ := by rfl

theorem innerLocal3 (L R : List Bool) : run0 table 2 ⟨4, ([true]) ++ ((L)), ([true,true]) ++ ((R))⟩ = some ⟨4, ([true]) ++ (([true,true]) ++ ((L))), (R)⟩ := by rfl

theorem innerStep3 (n j : Nat) : run0 table (2*n) ⟨4, ([true,true,false,true,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ = some ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [] [true,true] [true,true] 2 innerLocal3 n (([true,false,true,true]) ++ ((rep [true] j))) (([false,true,true]) ++ ((rep [true] j)))

theorem innerStep4 (n j : Nat) : run0 table 1 ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem innerEqL (n j : Nat) : (([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j))))) = (([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j))))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 1 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 true) ++ ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 1 true) j)))))))) = ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 1 true) j)))))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem innerRaw (n j : Nat) : run0 table (9+4*n) ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))), ([true,true]) ++ ((rep [true] j))⟩ := by

  have H := innerStep0 n j

  have H := join0 H (innerStep1 n j)

  have H := join0 H (innerStep2 n j)

  have H := join0 H (innerStep3 n j)

  have H := join0 H (innerStep4 n j)

  rw [show 3+2*n+5+2*n+1 = 9+4*n by omega] at H

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

theorem first (n : Nat) : run0 table (9+4*n) (family n) = some (middle n 0) := by
  simpa only [family,middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using firstRaw n

theorem inner (n j : Nat) : run0 table (9+4*n) (middle (n+1) j) = some (middle n (j+1)) := by
  simpa only [middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using innerRaw n j

theorem finish (j : Nat) : run0 table (12+j) (middle 0 j) = some (family (j+1)) := by
  simpa only [family,middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append,Nat.one_mul] using finishRaw j

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (cost 9 9 12 n) (family n) = some (family (n+1)) :=
  growthAll table 9 9 12 first inner finish n


theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (cost 9 9 12) entry (by intro n; unfold cost; omega) growth m hm
#print axioms never

#print axioms growth
end M8749

namespace M8751

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none

theorem firstStep0 (n : Nat) : run0 table 2 ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n)), []⟩ = some ⟨5, ([true,true,true]) ++ ((rep [true,true] n)), ([false,true])⟩ := by rfl

theorem firstLocal1 (L R : List Bool) : run0 table 2 ⟨5, ([true,true,true]) ++ (([true,true]) ++ ((L))), (R)⟩ = some ⟨5, ([true,true,true]) ++ ((L)), ([true,true]) ++ ((R))⟩ := by rfl

theorem firstStep1 (n : Nat) : run0 table (2*n) ⟨5, ([true,true,true]) ++ ((rep [true,true] n)), ([false,true])⟩ = some ⟨5, ([true,true,true]), (rep [true,true] n) ++ (([false,true]))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 5 [true,true,true] [] [true,true] [true,true] 2 firstLocal1 n ([]) (([false,true]))

theorem firstStep2 (n : Nat) : run0 table 6 ⟨5, ([true,true,true]), (rep [true,true] n) ++ (([false,true]))⟩ = some ⟨4, ([true,true,false,true]), (rep [true,true] n) ++ (([false,true]))⟩ := by rfl

theorem firstLocal3 (L R : List Bool) : run0 table 2 ⟨4, ([true]) ++ ((L)), ([true,true]) ++ ((R))⟩ = some ⟨4, ([true]) ++ (([true,true]) ++ ((L))), (R)⟩ := by rfl

theorem firstStep3 (n : Nat) : run0 table (2*n) ⟨4, ([true,true,false,true]), (rep [true,true] n) ++ (([false,true]))⟩ = some ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([false,true])⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [] [true,true] [true,true] 2 firstLocal3 n (([true,false,true])) (([false,true]))

theorem firstStep4 (n : Nat) : run0 table 1 ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([false,true])⟩ = some ⟨4, ([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([true])⟩ := by rfl

theorem firstEqL (n : Nat) : (([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true])))) = (([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true])))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 1 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 true) ++ ((List.replicate 1 false) ++ ((List.replicate 1 true))))))) = ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 false) ++ ((List.replicate 1 true))))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem firstRaw (n : Nat) : run0 table (9+4*n) ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n)), []⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true]))), ([true])⟩ := by

  have H := firstStep0 n

  have H := join0 H (firstStep1 n)

  have H := join0 H (firstStep2 n)

  have H := join0 H (firstStep3 n)

  have H := join0 H (firstStep4 n)

  rw [show 2+2*n+6+2*n+1 = 9+4*n by omega] at H

  rw [firstEqL n] at H

  exact H

theorem innerStep0 (n j : Nat) : run0 table 2 ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true]) ++ ((rep [true] j))⟩ = some ⟨5, ([true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem innerLocal1 (L R : List Bool) : run0 table 2 ⟨5, ([true,true,true]) ++ (([true,true]) ++ ((L))), (R)⟩ = some ⟨5, ([true,true,true]) ++ ((L)), ([true,true]) ++ ((R))⟩ := by rfl

theorem innerStep1 (n j : Nat) : run0 table (2*n) ⟨5, ([true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ = some ⟨5, ([true,true,true,false,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 5 [true,true,true] [] [true,true] [true,true] 2 innerLocal1 n (([false,true]) ++ ((rep [true] j))) (([false,true,true]) ++ ((rep [true] j)))

theorem innerStep2 (n j : Nat) : run0 table 6 ⟨5, ([true,true,true,false,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ = some ⟨4, ([true,true,false,true,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ := by rfl

theorem innerLocal3 (L R : List Bool) : run0 table 2 ⟨4, ([true]) ++ ((L)), ([true,true]) ++ ((R))⟩ = some ⟨4, ([true]) ++ (([true,true]) ++ ((L))), (R)⟩ := by rfl

theorem innerStep3 (n j : Nat) : run0 table (2*n) ⟨4, ([true,true,false,true,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ = some ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [] [true,true] [true,true] 2 innerLocal3 n (([true,false,true,true]) ++ ((rep [true] j))) (([false,true,true]) ++ ((rep [true] j)))

theorem innerStep4 (n j : Nat) : run0 table 1 ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem innerEqL (n j : Nat) : (([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j))))) = (([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j))))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 1 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 true) ++ ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 1 true) j)))))))) = ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 1 true) j)))))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem innerRaw (n j : Nat) : run0 table (9+4*n) ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))), ([true,true]) ++ ((rep [true] j))⟩ := by

  have H := innerStep0 n j

  have H := join0 H (innerStep1 n j)

  have H := join0 H (innerStep2 n j)

  have H := join0 H (innerStep3 n j)

  have H := join0 H (innerStep4 n j)

  rw [show 2+2*n+6+2*n+1 = 9+4*n by omega] at H

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

theorem first (n : Nat) : run0 table (9+4*n) (family n) = some (middle n 0) := by
  simpa only [family,middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using firstRaw n

theorem inner (n j : Nat) : run0 table (9+4*n) (middle (n+1) j) = some (middle n (j+1)) := by
  simpa only [middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using innerRaw n j

theorem finish (j : Nat) : run0 table (12+j) (middle 0 j) = some (family (j+1)) := by
  simpa only [family,middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append,Nat.one_mul] using finishRaw j

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (cost 9 9 12 n) (family n) = some (family (n+1)) :=
  growthAll table 9 9 12 first inner finish n


theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (cost 9 9 12) entry (by intro n; unfold cost; omega) growth m hm
#print axioms never

#print axioms growth
end M8751

namespace M8772

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

theorem firstStep0 (n : Nat) : run0 table 2 ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n)), []⟩ = some ⟨5, ([true,true,true]) ++ ((rep [true,true] n)), ([false,true])⟩ := by rfl

theorem firstLocal1 (L R : List Bool) : run0 table 2 ⟨5, ([true,true,true]) ++ (([true,true]) ++ ((L))), (R)⟩ = some ⟨5, ([true,true,true]) ++ ((L)), ([true,true]) ++ ((R))⟩ := by rfl

theorem firstStep1 (n : Nat) : run0 table (2*n) ⟨5, ([true,true,true]) ++ ((rep [true,true] n)), ([false,true])⟩ = some ⟨5, ([true,true,true]), (rep [true,true] n) ++ (([false,true]))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 5 [true,true,true] [] [true,true] [true,true] 2 firstLocal1 n ([]) (([false,true]))

theorem firstStep2 (n : Nat) : run0 table 8 ⟨5, ([true,true,true]), (rep [true,true] n) ++ (([false,true]))⟩ = some ⟨4, ([true,true,false,true]), (rep [true,true] n) ++ (([false,true]))⟩ := by rfl

theorem firstLocal3 (L R : List Bool) : run0 table 2 ⟨4, ([true]) ++ ((L)), ([true,true]) ++ ((R))⟩ = some ⟨4, ([true]) ++ (([true,true]) ++ ((L))), (R)⟩ := by rfl

theorem firstStep3 (n : Nat) : run0 table (2*n) ⟨4, ([true,true,false,true]), (rep [true,true] n) ++ (([false,true]))⟩ = some ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([false,true])⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [] [true,true] [true,true] 2 firstLocal3 n (([true,false,true])) (([false,true]))

theorem firstStep4 (n : Nat) : run0 table 1 ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([false,true])⟩ = some ⟨4, ([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([true])⟩ := by rfl

theorem firstEqL (n : Nat) : (([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true])))) = (([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true])))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 1 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 true) ++ ((List.replicate 1 false) ++ ((List.replicate 1 true))))))) = ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 false) ++ ((List.replicate 1 true))))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem firstRaw (n : Nat) : run0 table (11+4*n) ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n)), []⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true]))), ([true])⟩ := by

  have H := firstStep0 n

  have H := join0 H (firstStep1 n)

  have H := join0 H (firstStep2 n)

  have H := join0 H (firstStep3 n)

  have H := join0 H (firstStep4 n)

  rw [show 2+2*n+8+2*n+1 = 11+4*n by omega] at H

  rw [firstEqL n] at H

  exact H

theorem innerStep0 (n j : Nat) : run0 table 2 ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true]) ++ ((rep [true] j))⟩ = some ⟨5, ([true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem innerLocal1 (L R : List Bool) : run0 table 2 ⟨5, ([true,true,true]) ++ (([true,true]) ++ ((L))), (R)⟩ = some ⟨5, ([true,true,true]) ++ ((L)), ([true,true]) ++ ((R))⟩ := by rfl

theorem innerStep1 (n j : Nat) : run0 table (2*n) ⟨5, ([true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ = some ⟨5, ([true,true,true,false,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 5 [true,true,true] [] [true,true] [true,true] 2 innerLocal1 n (([false,true]) ++ ((rep [true] j))) (([false,true,true]) ++ ((rep [true] j)))

theorem innerStep2 (n j : Nat) : run0 table 8 ⟨5, ([true,true,true,false,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ = some ⟨4, ([true,true,false,true,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ := by rfl

theorem innerLocal3 (L R : List Bool) : run0 table 2 ⟨4, ([true]) ++ ((L)), ([true,true]) ++ ((R))⟩ = some ⟨4, ([true]) ++ (([true,true]) ++ ((L))), (R)⟩ := by rfl

theorem innerStep3 (n j : Nat) : run0 table (2*n) ⟨4, ([true,true,false,true,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ = some ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [] [true,true] [true,true] 2 innerLocal3 n (([true,false,true,true]) ++ ((rep [true] j))) (([false,true,true]) ++ ((rep [true] j)))

theorem innerStep4 (n j : Nat) : run0 table 1 ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem innerEqL (n j : Nat) : (([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j))))) = (([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j))))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 1 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 true) ++ ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 1 true) j)))))))) = ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 1 true) j)))))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem innerRaw (n j : Nat) : run0 table (11+4*n) ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))), ([true,true]) ++ ((rep [true] j))⟩ := by

  have H := innerStep0 n j

  have H := join0 H (innerStep1 n j)

  have H := join0 H (innerStep2 n j)

  have H := join0 H (innerStep3 n j)

  have H := join0 H (innerStep4 n j)

  rw [show 2+2*n+8+2*n+1 = 11+4*n by omega] at H

  rw [innerEqL n j] at H

  exact H

theorem finishStep0 (j : Nat) : run0 table 10 ⟨4, ([false,true,true,false,true]) ++ ((rep [true] j)), ([true]) ++ ((rep [true] j))⟩ = some ⟨4, ([true,true,true]) ++ ((rep [true] j)), ([true,true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem finishLocal1 (L R : List Bool) : run0 table 1 ⟨4, ([true]) ++ ((L)), ([true,true,true]) ++ (([true]) ++ ((R)))⟩ = some ⟨4, ([true]) ++ (([true]) ++ ((L))), ([true,true,true]) ++ ((R))⟩ := by rfl

theorem finishStep1 (j : Nat) : run0 table (1*j) ⟨4, ([true,true,true]) ++ ((rep [true] j)), ([true,true,true]) ++ ((rep [true] j))⟩ = some ⟨4, ([true]) ++ ((rep [true] j) ++ (([true,true]) ++ ((rep [true] j)))), ([true,true,true])⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [true,true,true] [true] [true] 1 finishLocal1 j (([true,true]) ++ ((rep [true] j))) ([])

theorem finishStep2 (j : Nat) : run0 table 4 ⟨4, ([true]) ++ ((rep [true] j) ++ (([true,true]) ++ ((rep [true] j)))), ([true,true,true])⟩ = some ⟨4, ([false,true,true,true,true]) ++ ((rep [true] j) ++ (([true,true]) ++ ((rep [true] j)))), []⟩ := by rfl

theorem finishEqL (j : Nat) : (([false,true,true,true,true]) ++ ((rep [true] j) ++ (([true,true]) ++ ((rep [true] j))))) = (([false,true,true,true,true,true,true]) ++ ((rep [true,true] j))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 4 true) ++ ((rep (List.replicate 1 true) j) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 1 true) j)))))) = ((List.replicate 1 false) ++ ((List.replicate 6 true) ++ ((rep (List.replicate 2 true) j))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem finishRaw (j : Nat) : run0 table (14+1*j) ⟨4, ([false,true,true,false,true]) ++ ((rep [true] j)), ([true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true,true,true,true,true,true]) ++ ((rep [true,true] j)), []⟩ := by

  have H := finishStep0 j

  have H := join0 H (finishStep1 j)

  have H := join0 H (finishStep2 j)

  rw [show 10+1*j+4 = 14+1*j by omega] at H

  rw [finishEqL j] at H

  exact H

theorem first (n : Nat) : run0 table (11+4*n) (family n) = some (middle n 0) := by
  simpa only [family,middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using firstRaw n

theorem inner (n j : Nat) : run0 table (11+4*n) (middle (n+1) j) = some (middle n (j+1)) := by
  simpa only [middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using innerRaw n j

theorem finish (j : Nat) : run0 table (14+j) (middle 0 j) = some (family (j+1)) := by
  simpa only [family,middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append,Nat.one_mul] using finishRaw j

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (cost 11 11 14 n) (family n) = some (family (n+1)) :=
  growthAll table 11 11 14 first inner finish n


theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (cost 11 11 14) entry (by intro n; unfold cost; omega) growth m hm
#print axioms never

#print axioms growth
end M8772

namespace M8785

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

theorem firstStep0 (n : Nat) : run0 table 2 ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n)), []⟩ = some ⟨5, ([true,true,true]) ++ ((rep [true,true] n)), ([false,true])⟩ := by rfl

theorem firstLocal1 (L R : List Bool) : run0 table 2 ⟨5, ([true,true,true]) ++ (([true,true]) ++ ((L))), (R)⟩ = some ⟨5, ([true,true,true]) ++ ((L)), ([true,true]) ++ ((R))⟩ := by rfl

theorem firstStep1 (n : Nat) : run0 table (2*n) ⟨5, ([true,true,true]) ++ ((rep [true,true] n)), ([false,true])⟩ = some ⟨5, ([true,true,true]), (rep [true,true] n) ++ (([false,true]))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 5 [true,true,true] [] [true,true] [true,true] 2 firstLocal1 n ([]) (([false,true]))

theorem firstStep2 (n : Nat) : run0 table 6 ⟨5, ([true,true,true]), (rep [true,true] n) ++ (([false,true]))⟩ = some ⟨4, ([true,true,false,true]), (rep [true,true] n) ++ (([false,true]))⟩ := by rfl

theorem firstLocal3 (L R : List Bool) : run0 table 2 ⟨4, ([true]) ++ ((L)), ([true,true]) ++ ((R))⟩ = some ⟨4, ([true]) ++ (([true,true]) ++ ((L))), (R)⟩ := by rfl

theorem firstStep3 (n : Nat) : run0 table (2*n) ⟨4, ([true,true,false,true]), (rep [true,true] n) ++ (([false,true]))⟩ = some ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([false,true])⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [] [true,true] [true,true] 2 firstLocal3 n (([true,false,true])) (([false,true]))

theorem firstStep4 (n : Nat) : run0 table 1 ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([false,true])⟩ = some ⟨4, ([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([true])⟩ := by rfl

theorem firstEqL (n : Nat) : (([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true])))) = (([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true])))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 1 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 true) ++ ((List.replicate 1 false) ++ ((List.replicate 1 true))))))) = ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 false) ++ ((List.replicate 1 true))))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem firstRaw (n : Nat) : run0 table (9+4*n) ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n)), []⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true]))), ([true])⟩ := by

  have H := firstStep0 n

  have H := join0 H (firstStep1 n)

  have H := join0 H (firstStep2 n)

  have H := join0 H (firstStep3 n)

  have H := join0 H (firstStep4 n)

  rw [show 2+2*n+6+2*n+1 = 9+4*n by omega] at H

  rw [firstEqL n] at H

  exact H

theorem innerStep0 (n j : Nat) : run0 table 2 ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true]) ++ ((rep [true] j))⟩ = some ⟨5, ([true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem innerLocal1 (L R : List Bool) : run0 table 2 ⟨5, ([true,true,true]) ++ (([true,true]) ++ ((L))), (R)⟩ = some ⟨5, ([true,true,true]) ++ ((L)), ([true,true]) ++ ((R))⟩ := by rfl

theorem innerStep1 (n j : Nat) : run0 table (2*n) ⟨5, ([true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ = some ⟨5, ([true,true,true,false,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 5 [true,true,true] [] [true,true] [true,true] 2 innerLocal1 n (([false,true]) ++ ((rep [true] j))) (([false,true,true]) ++ ((rep [true] j)))

theorem innerStep2 (n j : Nat) : run0 table 6 ⟨5, ([true,true,true,false,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ = some ⟨4, ([true,true,false,true,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ := by rfl

theorem innerLocal3 (L R : List Bool) : run0 table 2 ⟨4, ([true]) ++ ((L)), ([true,true]) ++ ((R))⟩ = some ⟨4, ([true]) ++ (([true,true]) ++ ((L))), (R)⟩ := by rfl

theorem innerStep3 (n j : Nat) : run0 table (2*n) ⟨4, ([true,true,false,true,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ = some ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [] [true,true] [true,true] 2 innerLocal3 n (([true,false,true,true]) ++ ((rep [true] j))) (([false,true,true]) ++ ((rep [true] j)))

theorem innerStep4 (n j : Nat) : run0 table 1 ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem innerEqL (n j : Nat) : (([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j))))) = (([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j))))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 1 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 true) ++ ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 1 true) j)))))))) = ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 1 true) j)))))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem innerRaw (n j : Nat) : run0 table (9+4*n) ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))), ([true,true]) ++ ((rep [true] j))⟩ := by

  have H := innerStep0 n j

  have H := join0 H (innerStep1 n j)

  have H := join0 H (innerStep2 n j)

  have H := join0 H (innerStep3 n j)

  have H := join0 H (innerStep4 n j)

  rw [show 2+2*n+6+2*n+1 = 9+4*n by omega] at H

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

theorem first (n : Nat) : run0 table (9+4*n) (family n) = some (middle n 0) := by
  simpa only [family,middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using firstRaw n

theorem inner (n j : Nat) : run0 table (9+4*n) (middle (n+1) j) = some (middle n (j+1)) := by
  simpa only [middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using innerRaw n j

theorem finish (j : Nat) : run0 table (12+j) (middle 0 j) = some (family (j+1)) := by
  simpa only [family,middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append,Nat.one_mul] using finishRaw j

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (cost 9 9 12 n) (family n) = some (family (n+1)) :=
  growthAll table 9 9 12 first inner finish n


theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (cost 9 9 12) entry (by intro n; unfold cost; omega) growth m hm
#print axioms never

#print axioms growth
end M8785

namespace M9751

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

theorem firstStep0 (n : Nat) : run0 table 2 ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n)), []⟩ = some ⟨0, ([true,true,true]) ++ ((rep [true,true] n)), ([false,true])⟩ := by rfl

theorem firstLocal1 (L R : List Bool) : run0 table 2 ⟨0, ([true,true,true]) ++ (([true,true]) ++ ((L))), (R)⟩ = some ⟨0, ([true,true,true]) ++ ((L)), ([true,true]) ++ ((R))⟩ := by rfl

theorem firstStep1 (n : Nat) : run0 table (2*n) ⟨0, ([true,true,true]) ++ ((rep [true,true] n)), ([false,true])⟩ = some ⟨0, ([true,true,true]), (rep [true,true] n) ++ (([false,true]))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 0 [true,true,true] [] [true,true] [true,true] 2 firstLocal1 n ([]) (([false,true]))

theorem firstStep2 (n : Nat) : run0 table 6 ⟨0, ([true,true,true]), (rep [true,true] n) ++ (([false,true]))⟩ = some ⟨4, ([true,true,false,true]), (rep [true,true] n) ++ (([false,true]))⟩ := by rfl

theorem firstLocal3 (L R : List Bool) : run0 table 2 ⟨4, ([true]) ++ ((L)), ([true,true]) ++ ((R))⟩ = some ⟨4, ([true]) ++ (([true,true]) ++ ((L))), (R)⟩ := by rfl

theorem firstStep3 (n : Nat) : run0 table (2*n) ⟨4, ([true,true,false,true]), (rep [true,true] n) ++ (([false,true]))⟩ = some ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([false,true])⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [] [true,true] [true,true] 2 firstLocal3 n (([true,false,true])) (([false,true]))

theorem firstStep4 (n : Nat) : run0 table 1 ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([false,true])⟩ = some ⟨4, ([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true]))), ([true])⟩ := by rfl

theorem firstEqL (n : Nat) : (([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true])))) = (([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true])))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 1 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 true) ++ ((List.replicate 1 false) ++ ((List.replicate 1 true))))))) = ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 false) ++ ((List.replicate 1 true))))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem firstRaw (n : Nat) : run0 table (9+4*n) ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n)), []⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true]))), ([true])⟩ := by

  have H := firstStep0 n

  have H := join0 H (firstStep1 n)

  have H := join0 H (firstStep2 n)

  have H := join0 H (firstStep3 n)

  have H := join0 H (firstStep4 n)

  rw [show 2+2*n+6+2*n+1 = 9+4*n by omega] at H

  rw [firstEqL n] at H

  exact H

theorem innerStep0 (n j : Nat) : run0 table 2 ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true]) ++ ((rep [true] j))⟩ = some ⟨0, ([true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem innerLocal1 (L R : List Bool) : run0 table 2 ⟨0, ([true,true,true]) ++ (([true,true]) ++ ((L))), (R)⟩ = some ⟨0, ([true,true,true]) ++ ((L)), ([true,true]) ++ ((R))⟩ := by rfl

theorem innerStep1 (n j : Nat) : run0 table (2*n) ⟨0, ([true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ = some ⟨0, ([true,true,true,false,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 0 [true,true,true] [] [true,true] [true,true] 2 innerLocal1 n (([false,true]) ++ ((rep [true] j))) (([false,true,true]) ++ ((rep [true] j)))

theorem innerStep2 (n j : Nat) : run0 table 6 ⟨0, ([true,true,true,false,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ = some ⟨4, ([true,true,false,true,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ := by rfl

theorem innerLocal3 (L R : List Bool) : run0 table 2 ⟨4, ([true]) ++ ((L)), ([true,true]) ++ ((R))⟩ = some ⟨4, ([true]) ++ (([true,true]) ++ ((L))), (R)⟩ := by rfl

theorem innerStep3 (n j : Nat) : run0 table (2*n) ⟨4, ([true,true,false,true,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ = some ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [] [true,true] [true,true] 2 innerLocal3 n (([true,false,true,true]) ++ ((rep [true] j))) (([false,true,true]) ++ ((rep [true] j)))

theorem innerStep4 (n j : Nat) : run0 table 1 ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j)))), ([true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem innerEqL (n j : Nat) : (([false,true]) ++ ((rep [true,true] n) ++ (([true,false,true,true]) ++ ((rep [true] j))))) = (([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j))))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 1 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 true) ++ ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 1 true) j)))))))) = ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 2 true) n) ++ ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 1 true) j)))))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem innerRaw (n j : Nat) : run0 table (9+4*n) ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))), ([true,true]) ++ ((rep [true] j))⟩ := by

  have H := innerStep0 n j

  have H := join0 H (innerStep1 n j)

  have H := join0 H (innerStep2 n j)

  have H := join0 H (innerStep3 n j)

  have H := join0 H (innerStep4 n j)

  rw [show 2+2*n+6+2*n+1 = 9+4*n by omega] at H

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

theorem first (n : Nat) : run0 table (9+4*n) (family n) = some (middle n 0) := by
  simpa only [family,middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using firstRaw n

theorem inner (n j : Nat) : run0 table (9+4*n) (middle (n+1) j) = some (middle n (j+1)) := by
  simpa only [middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using innerRaw n j

theorem finish (j : Nat) : run0 table (12+j) (middle 0 j) = some (family (j+1)) := by
  simpa only [family,middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append,Nat.one_mul] using finishRaw j

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (cost 9 9 12 n) (family n) = some (family (n+1)) :=
  growthAll table 9 9 12 first inner finish n


theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (cost 9 9 12) entry (by intro n; unfold cost; omega) growth m hm
#print axioms never

#print axioms growth
end M9751

namespace M9752

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,false,3⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

theorem firstStep0 (n : Nat) : run0 table 2 ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n)), []⟩ = some ⟨0, ([true,true,true]) ++ ((rep [true,true] n)), ([false,true])⟩ := by rfl

theorem firstLocal1 (L R : List Bool) : run0 table 2 ⟨0, ([true,true,true]) ++ (([true,true]) ++ ((L))), (R)⟩ = some ⟨0, ([true,true,true]) ++ ((L)), ([true,true]) ++ ((R))⟩ := by rfl

theorem firstStep1 (n : Nat) : run0 table (2*n) ⟨0, ([true,true,true]) ++ ((rep [true,true] n)), ([false,true])⟩ = some ⟨0, ([true,true,true]), (rep [true,true] n) ++ (([false,true]))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 0 [true,true,true] [] [true,true] [true,true] 2 firstLocal1 n ([]) (([false,true]))

theorem firstStep2 (n : Nat) : run0 table 5 ⟨0, ([true,true,true]), (rep [true,true] n) ++ (([false,true]))⟩ = some ⟨4, ([true,false,true]), ([true]) ++ ((rep [true,true] n) ++ (([false,true])))⟩ := by rfl

theorem firstLocal3 (L R : List Bool) : run0 table 2 ⟨4, ([true]) ++ ((L)), ([true]) ++ (([true,true]) ++ ((R)))⟩ = some ⟨4, ([true]) ++ (([true,true]) ++ ((L))), ([true]) ++ ((R))⟩ := by rfl

theorem firstStep3 (n : Nat) : run0 table (2*n) ⟨4, ([true,false,true]), ([true]) ++ ((rep [true,true] n) ++ (([false,true])))⟩ = some ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([false,true]))), ([true,false,true])⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [true] [true,true] [true,true] 2 firstLocal3 n (([false,true])) (([false,true]))

theorem firstStep4 (n : Nat) : run0 table 2 ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([false,true]))), ([true,false,true])⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true]))), ([true])⟩ := by rfl

theorem firstRaw (n : Nat) : run0 table (9+4*n) ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n)), []⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true]))), ([true])⟩ := by

  have H := firstStep0 n

  have H := join0 H (firstStep1 n)

  have H := join0 H (firstStep2 n)

  have H := join0 H (firstStep3 n)

  have H := join0 H (firstStep4 n)

  rw [show 2+2*n+5+2*n+2 = 9+4*n by omega] at H

  exact H

theorem innerStep0 (n j : Nat) : run0 table 2 ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true]) ++ ((rep [true] j))⟩ = some ⟨0, ([true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem innerLocal1 (L R : List Bool) : run0 table 2 ⟨0, ([true,true,true]) ++ (([true,true]) ++ ((L))), (R)⟩ = some ⟨0, ([true,true,true]) ++ ((L)), ([true,true]) ++ ((R))⟩ := by rfl

theorem innerStep1 (n j : Nat) : run0 table (2*n) ⟨0, ([true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ = some ⟨0, ([true,true,true,false,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 0 [true,true,true] [] [true,true] [true,true] 2 innerLocal1 n (([false,true]) ++ ((rep [true] j))) (([false,true,true]) ++ ((rep [true] j)))

theorem innerStep2 (n j : Nat) : run0 table 5 ⟨0, ([true,true,true,false,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ = some ⟨4, ([true,false,true,true]) ++ ((rep [true] j)), ([true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j))))⟩ := by rfl

theorem innerLocal3 (L R : List Bool) : run0 table 2 ⟨4, ([true]) ++ ((L)), ([true]) ++ (([true,true]) ++ ((R)))⟩ = some ⟨4, ([true]) ++ (([true,true]) ++ ((L))), ([true]) ++ ((R))⟩ := by rfl

theorem innerStep3 (n j : Nat) : run0 table (2*n) ⟨4, ([true,false,true,true]) ++ ((rep [true] j)), ([true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j))))⟩ = some ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))), ([true,false,true,true]) ++ ((rep [true] j))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [true] [true,true] [true,true] 2 innerLocal3 n (([false,true,true]) ++ ((rep [true] j))) (([false,true,true]) ++ ((rep [true] j)))

theorem innerStep4 (n j : Nat) : run0 table 2 ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))), ([true,false,true,true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))), ([true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem innerRaw (n j : Nat) : run0 table (9+4*n) ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))), ([true,true]) ++ ((rep [true] j))⟩ := by

  have H := innerStep0 n j

  have H := join0 H (innerStep1 n j)

  have H := join0 H (innerStep2 n j)

  have H := join0 H (innerStep3 n j)

  have H := join0 H (innerStep4 n j)

  rw [show 2+2*n+5+2*n+2 = 9+4*n by omega] at H

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

theorem first (n : Nat) : run0 table (9+4*n) (family n) = some (middle n 0) := by
  simpa only [family,middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using firstRaw n

theorem inner (n j : Nat) : run0 table (9+4*n) (middle (n+1) j) = some (middle n (j+1)) := by
  simpa only [middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using innerRaw n j

theorem finish (j : Nat) : run0 table (12+j) (middle 0 j) = some (family (j+1)) := by
  simpa only [family,middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append,Nat.one_mul] using finishRaw j

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (cost 9 9 12 n) (family n) = some (family (n+1)) :=
  growthAll table 9 9 12 first inner finish n


theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (cost 9 9 12) entry (by intro n; unfold cost; omega) growth m hm
#print axioms never

#print axioms growth
end M9752

namespace M9753

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

theorem firstStep0 (n : Nat) : run0 table 2 ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n)), []⟩ = some ⟨0, ([true,true,true]) ++ ((rep [true,true] n)), ([false,true])⟩ := by rfl

theorem firstLocal1 (L R : List Bool) : run0 table 2 ⟨0, ([true,true,true]) ++ (([true,true]) ++ ((L))), (R)⟩ = some ⟨0, ([true,true,true]) ++ ((L)), ([true,true]) ++ ((R))⟩ := by rfl

theorem firstStep1 (n : Nat) : run0 table (2*n) ⟨0, ([true,true,true]) ++ ((rep [true,true] n)), ([false,true])⟩ = some ⟨0, ([true,true,true]), (rep [true,true] n) ++ (([false,true]))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 0 [true,true,true] [] [true,true] [true,true] 2 firstLocal1 n ([]) (([false,true]))

theorem firstStep2 (n : Nat) : run0 table 5 ⟨0, ([true,true,true]), (rep [true,true] n) ++ (([false,true]))⟩ = some ⟨4, ([true,false,true]), ([true]) ++ ((rep [true,true] n) ++ (([false,true])))⟩ := by rfl

theorem firstLocal3 (L R : List Bool) : run0 table 2 ⟨4, ([true]) ++ ((L)), ([true]) ++ (([true,true]) ++ ((R)))⟩ = some ⟨4, ([true]) ++ (([true,true]) ++ ((L))), ([true]) ++ ((R))⟩ := by rfl

theorem firstStep3 (n : Nat) : run0 table (2*n) ⟨4, ([true,false,true]), ([true]) ++ ((rep [true,true] n) ++ (([false,true])))⟩ = some ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([false,true]))), ([true,false,true])⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [true] [true,true] [true,true] 2 firstLocal3 n (([false,true])) (([false,true]))

theorem firstStep4 (n : Nat) : run0 table 2 ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([false,true]))), ([true,false,true])⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true]))), ([true])⟩ := by rfl

theorem firstRaw (n : Nat) : run0 table (9+4*n) ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n)), []⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true]))), ([true])⟩ := by

  have H := firstStep0 n

  have H := join0 H (firstStep1 n)

  have H := join0 H (firstStep2 n)

  have H := join0 H (firstStep3 n)

  have H := join0 H (firstStep4 n)

  rw [show 2+2*n+5+2*n+2 = 9+4*n by omega] at H

  exact H

theorem innerStep0 (n j : Nat) : run0 table 2 ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true]) ++ ((rep [true] j))⟩ = some ⟨0, ([true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem innerLocal1 (L R : List Bool) : run0 table 2 ⟨0, ([true,true,true]) ++ (([true,true]) ++ ((L))), (R)⟩ = some ⟨0, ([true,true,true]) ++ ((L)), ([true,true]) ++ ((R))⟩ := by rfl

theorem innerStep1 (n j : Nat) : run0 table (2*n) ⟨0, ([true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ = some ⟨0, ([true,true,true,false,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 0 [true,true,true] [] [true,true] [true,true] 2 innerLocal1 n (([false,true]) ++ ((rep [true] j))) (([false,true,true]) ++ ((rep [true] j)))

theorem innerStep2 (n j : Nat) : run0 table 5 ⟨0, ([true,true,true,false,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ = some ⟨4, ([true,false,true,true]) ++ ((rep [true] j)), ([true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j))))⟩ := by rfl

theorem innerLocal3 (L R : List Bool) : run0 table 2 ⟨4, ([true]) ++ ((L)), ([true]) ++ (([true,true]) ++ ((R)))⟩ = some ⟨4, ([true]) ++ (([true,true]) ++ ((L))), ([true]) ++ ((R))⟩ := by rfl

theorem innerStep3 (n j : Nat) : run0 table (2*n) ⟨4, ([true,false,true,true]) ++ ((rep [true] j)), ([true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j))))⟩ = some ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))), ([true,false,true,true]) ++ ((rep [true] j))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [true] [true,true] [true,true] 2 innerLocal3 n (([false,true,true]) ++ ((rep [true] j))) (([false,true,true]) ++ ((rep [true] j)))

theorem innerStep4 (n j : Nat) : run0 table 2 ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))), ([true,false,true,true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))), ([true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem innerRaw (n j : Nat) : run0 table (9+4*n) ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))), ([true,true]) ++ ((rep [true] j))⟩ := by

  have H := innerStep0 n j

  have H := join0 H (innerStep1 n j)

  have H := join0 H (innerStep2 n j)

  have H := join0 H (innerStep3 n j)

  have H := join0 H (innerStep4 n j)

  rw [show 2+2*n+5+2*n+2 = 9+4*n by omega] at H

  exact H

theorem finishStep0 (j : Nat) : run0 table 7 ⟨4, ([false,true,true,false,true]) ++ ((rep [true] j)), ([true]) ++ ((rep [true] j))⟩ = some ⟨4, ([true,true]) ++ ((rep [true] j)), ([true,true,true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem finishLocal1 (L R : List Bool) : run0 table 1 ⟨4, ([true]) ++ ((L)), ([true,true,true,true]) ++ (([true]) ++ ((R)))⟩ = some ⟨4, ([true]) ++ (([true]) ++ ((L))), ([true,true,true,true]) ++ ((R))⟩ := by rfl

theorem finishStep1 (j : Nat) : run0 table (1*j) ⟨4, ([true,true]) ++ ((rep [true] j)), ([true,true,true,true]) ++ ((rep [true] j))⟩ = some ⟨4, ([true]) ++ ((rep [true] j) ++ (([true]) ++ ((rep [true] j)))), ([true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [true,true,true,true] [true] [true] 1 finishLocal1 j (([true]) ++ ((rep [true] j))) ([])

theorem finishStep2 (j : Nat) : run0 table 5 ⟨4, ([true]) ++ ((rep [true] j) ++ (([true]) ++ ((rep [true] j)))), ([true,true,true,true])⟩ = some ⟨4, ([false,true,true,true,true,true]) ++ ((rep [true] j) ++ (([true]) ++ ((rep [true] j)))), []⟩ := by rfl

theorem finishEqL (j : Nat) : (([false,true,true,true,true,true]) ++ ((rep [true] j) ++ (([true]) ++ ((rep [true] j))))) = (([false,true,true,true,true,true,true]) ++ ((rep [true,true] j))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 5 true) ++ ((rep (List.replicate 1 true) j) ++ ((List.replicate 1 true) ++ ((rep (List.replicate 1 true) j)))))) = ((List.replicate 1 false) ++ ((List.replicate 6 true) ++ ((rep (List.replicate 2 true) j))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem finishRaw (j : Nat) : run0 table (12+1*j) ⟨4, ([false,true,true,false,true]) ++ ((rep [true] j)), ([true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true,true,true,true,true,true]) ++ ((rep [true,true] j)), []⟩ := by

  have H := finishStep0 j

  have H := join0 H (finishStep1 j)

  have H := join0 H (finishStep2 j)

  rw [show 7+1*j+5 = 12+1*j by omega] at H

  rw [finishEqL j] at H

  exact H

theorem first (n : Nat) : run0 table (9+4*n) (family n) = some (middle n 0) := by
  simpa only [family,middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using firstRaw n

theorem inner (n j : Nat) : run0 table (9+4*n) (middle (n+1) j) = some (middle n (j+1)) := by
  simpa only [middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using innerRaw n j

theorem finish (j : Nat) : run0 table (12+j) (middle 0 j) = some (family (j+1)) := by
  simpa only [family,middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append,Nat.one_mul] using finishRaw j

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (cost 9 9 12 n) (family n) = some (family (n+1)) :=
  growthAll table 9 9 12 first inner finish n


theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (cost 9 9 12) entry (by intro n; unfold cost; omega) growth m hm
#print axioms never

#print axioms growth
end M9753

namespace M9754

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

theorem firstStep0 (n : Nat) : run0 table 2 ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n)), []⟩ = some ⟨0, ([true,true,true]) ++ ((rep [true,true] n)), ([false,true])⟩ := by rfl

theorem firstLocal1 (L R : List Bool) : run0 table 2 ⟨0, ([true,true,true]) ++ (([true,true]) ++ ((L))), (R)⟩ = some ⟨0, ([true,true,true]) ++ ((L)), ([true,true]) ++ ((R))⟩ := by rfl

theorem firstStep1 (n : Nat) : run0 table (2*n) ⟨0, ([true,true,true]) ++ ((rep [true,true] n)), ([false,true])⟩ = some ⟨0, ([true,true,true]), (rep [true,true] n) ++ (([false,true]))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 0 [true,true,true] [] [true,true] [true,true] 2 firstLocal1 n ([]) (([false,true]))

theorem firstStep2 (n : Nat) : run0 table 5 ⟨0, ([true,true,true]), (rep [true,true] n) ++ (([false,true]))⟩ = some ⟨4, ([true,false,true]), ([true]) ++ ((rep [true,true] n) ++ (([false,true])))⟩ := by rfl

theorem firstLocal3 (L R : List Bool) : run0 table 2 ⟨4, ([true]) ++ ((L)), ([true]) ++ (([true,true]) ++ ((R)))⟩ = some ⟨4, ([true]) ++ (([true,true]) ++ ((L))), ([true]) ++ ((R))⟩ := by rfl

theorem firstStep3 (n : Nat) : run0 table (2*n) ⟨4, ([true,false,true]), ([true]) ++ ((rep [true,true] n) ++ (([false,true])))⟩ = some ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([false,true]))), ([true,false,true])⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [true] [true,true] [true,true] 2 firstLocal3 n (([false,true])) (([false,true]))

theorem firstStep4 (n : Nat) : run0 table 2 ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([false,true]))), ([true,false,true])⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true]))), ([true])⟩ := by rfl

theorem firstRaw (n : Nat) : run0 table (9+4*n) ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n)), []⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true]))), ([true])⟩ := by

  have H := firstStep0 n

  have H := join0 H (firstStep1 n)

  have H := join0 H (firstStep2 n)

  have H := join0 H (firstStep3 n)

  have H := join0 H (firstStep4 n)

  rw [show 2+2*n+5+2*n+2 = 9+4*n by omega] at H

  exact H

theorem innerStep0 (n j : Nat) : run0 table 2 ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true]) ++ ((rep [true] j))⟩ = some ⟨0, ([true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem innerLocal1 (L R : List Bool) : run0 table 2 ⟨0, ([true,true,true]) ++ (([true,true]) ++ ((L))), (R)⟩ = some ⟨0, ([true,true,true]) ++ ((L)), ([true,true]) ++ ((R))⟩ := by rfl

theorem innerStep1 (n j : Nat) : run0 table (2*n) ⟨0, ([true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ = some ⟨0, ([true,true,true,false,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 0 [true,true,true] [] [true,true] [true,true] 2 innerLocal1 n (([false,true]) ++ ((rep [true] j))) (([false,true,true]) ++ ((rep [true] j)))

theorem innerStep2 (n j : Nat) : run0 table 5 ⟨0, ([true,true,true,false,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ = some ⟨4, ([true,false,true,true]) ++ ((rep [true] j)), ([true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j))))⟩ := by rfl

theorem innerLocal3 (L R : List Bool) : run0 table 2 ⟨4, ([true]) ++ ((L)), ([true]) ++ (([true,true]) ++ ((R)))⟩ = some ⟨4, ([true]) ++ (([true,true]) ++ ((L))), ([true]) ++ ((R))⟩ := by rfl

theorem innerStep3 (n j : Nat) : run0 table (2*n) ⟨4, ([true,false,true,true]) ++ ((rep [true] j)), ([true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j))))⟩ = some ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))), ([true,false,true,true]) ++ ((rep [true] j))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [true] [true,true] [true,true] 2 innerLocal3 n (([false,true,true]) ++ ((rep [true] j))) (([false,true,true]) ++ ((rep [true] j)))

theorem innerStep4 (n j : Nat) : run0 table 2 ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))), ([true,false,true,true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))), ([true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem innerRaw (n j : Nat) : run0 table (9+4*n) ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))), ([true,true]) ++ ((rep [true] j))⟩ := by

  have H := innerStep0 n j

  have H := join0 H (innerStep1 n j)

  have H := join0 H (innerStep2 n j)

  have H := join0 H (innerStep3 n j)

  have H := join0 H (innerStep4 n j)

  rw [show 2+2*n+5+2*n+2 = 9+4*n by omega] at H

  exact H

theorem finishStep0 (j : Nat) : run0 table 8 ⟨4, ([false,true,true,false,true]) ++ ((rep [true] j)), ([true]) ++ ((rep [true] j))⟩ = some ⟨4, ([true,true,true,true,true]) ++ ((rep [true] j)), ([true]) ++ ((rep [true] j))⟩ := by rfl

theorem finishLocal1 (L R : List Bool) : run0 table 1 ⟨4, ([true]) ++ ((L)), ([true]) ++ (([true]) ++ ((R)))⟩ = some ⟨4, ([true]) ++ (([true]) ++ ((L))), ([true]) ++ ((R))⟩ := by rfl

theorem finishStep1 (j : Nat) : run0 table (1*j) ⟨4, ([true,true,true,true,true]) ++ ((rep [true] j)), ([true]) ++ ((rep [true] j))⟩ = some ⟨4, ([true]) ++ ((rep [true] j) ++ (([true,true,true,true]) ++ ((rep [true] j)))), ([true])⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [true] [true] [true] 1 finishLocal1 j (([true,true,true,true]) ++ ((rep [true] j))) ([])

theorem finishStep2 (j : Nat) : run0 table 2 ⟨4, ([true]) ++ ((rep [true] j) ++ (([true,true,true,true]) ++ ((rep [true] j)))), ([true])⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true] j) ++ (([true,true,true,true]) ++ ((rep [true] j)))), []⟩ := by rfl

theorem finishEqL (j : Nat) : (([false,true,true]) ++ ((rep [true] j) ++ (([true,true,true,true]) ++ ((rep [true] j))))) = (([false,true,true,true,true,true,true]) ++ ((rep [true,true] j))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 2 true) ++ ((rep (List.replicate 1 true) j) ++ ((List.replicate 4 true) ++ ((rep (List.replicate 1 true) j)))))) = ((List.replicate 1 false) ++ ((List.replicate 6 true) ++ ((rep (List.replicate 2 true) j))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem finishRaw (j : Nat) : run0 table (10+1*j) ⟨4, ([false,true,true,false,true]) ++ ((rep [true] j)), ([true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true,true,true,true,true,true]) ++ ((rep [true,true] j)), []⟩ := by

  have H := finishStep0 j

  have H := join0 H (finishStep1 j)

  have H := join0 H (finishStep2 j)

  rw [show 8+1*j+2 = 10+1*j by omega] at H

  rw [finishEqL j] at H

  exact H

theorem first (n : Nat) : run0 table (9+4*n) (family n) = some (middle n 0) := by
  simpa only [family,middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using firstRaw n

theorem inner (n j : Nat) : run0 table (9+4*n) (middle (n+1) j) = some (middle n (j+1)) := by
  simpa only [middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using innerRaw n j

theorem finish (j : Nat) : run0 table (10+j) (middle 0 j) = some (family (j+1)) := by
  simpa only [family,middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append,Nat.one_mul] using finishRaw j

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (cost 9 9 10 n) (family n) = some (family (n+1)) :=
  growthAll table 9 9 10 first inner finish n


theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (cost 9 9 10) entry (by intro n; unfold cost; omega) growth m hm
#print axioms never

#print axioms growth
end M9754

namespace M9755

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

theorem firstStep0 (n : Nat) : run0 table 2 ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n)), []⟩ = some ⟨0, ([true,true,true]) ++ ((rep [true,true] n)), ([false,true])⟩ := by rfl

theorem firstLocal1 (L R : List Bool) : run0 table 2 ⟨0, ([true,true,true]) ++ (([true,true]) ++ ((L))), (R)⟩ = some ⟨0, ([true,true,true]) ++ ((L)), ([true,true]) ++ ((R))⟩ := by rfl

theorem firstStep1 (n : Nat) : run0 table (2*n) ⟨0, ([true,true,true]) ++ ((rep [true,true] n)), ([false,true])⟩ = some ⟨0, ([true,true,true]), (rep [true,true] n) ++ (([false,true]))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 0 [true,true,true] [] [true,true] [true,true] 2 firstLocal1 n ([]) (([false,true]))

theorem firstStep2 (n : Nat) : run0 table 5 ⟨0, ([true,true,true]), (rep [true,true] n) ++ (([false,true]))⟩ = some ⟨4, ([true,false,true]), ([true]) ++ ((rep [true,true] n) ++ (([false,true])))⟩ := by rfl

theorem firstLocal3 (L R : List Bool) : run0 table 2 ⟨4, ([true]) ++ ((L)), ([true]) ++ (([true,true]) ++ ((R)))⟩ = some ⟨4, ([true]) ++ (([true,true]) ++ ((L))), ([true]) ++ ((R))⟩ := by rfl

theorem firstStep3 (n : Nat) : run0 table (2*n) ⟨4, ([true,false,true]), ([true]) ++ ((rep [true,true] n) ++ (([false,true])))⟩ = some ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([false,true]))), ([true,false,true])⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [true] [true,true] [true,true] 2 firstLocal3 n (([false,true])) (([false,true]))

theorem firstStep4 (n : Nat) : run0 table 2 ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([false,true]))), ([true,false,true])⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true]))), ([true])⟩ := by rfl

theorem firstRaw (n : Nat) : run0 table (9+4*n) ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n)), []⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true]))), ([true])⟩ := by

  have H := firstStep0 n

  have H := join0 H (firstStep1 n)

  have H := join0 H (firstStep2 n)

  have H := join0 H (firstStep3 n)

  have H := join0 H (firstStep4 n)

  rw [show 2+2*n+5+2*n+2 = 9+4*n by omega] at H

  exact H

theorem innerStep0 (n j : Nat) : run0 table 2 ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true]) ++ ((rep [true] j))⟩ = some ⟨0, ([true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem innerLocal1 (L R : List Bool) : run0 table 2 ⟨0, ([true,true,true]) ++ (([true,true]) ++ ((L))), (R)⟩ = some ⟨0, ([true,true,true]) ++ ((L)), ([true,true]) ++ ((R))⟩ := by rfl

theorem innerStep1 (n j : Nat) : run0 table (2*n) ⟨0, ([true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([false,true,true]) ++ ((rep [true] j))⟩ = some ⟨0, ([true,true,true,false,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepL table 0 [true,true,true] [] [true,true] [true,true] 2 innerLocal1 n (([false,true]) ++ ((rep [true] j))) (([false,true,true]) ++ ((rep [true] j)))

theorem innerStep2 (n j : Nat) : run0 table 5 ⟨0, ([true,true,true,false,true]) ++ ((rep [true] j)), (rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))⟩ = some ⟨4, ([true,false,true,true]) ++ ((rep [true] j)), ([true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j))))⟩ := by rfl

theorem innerLocal3 (L R : List Bool) : run0 table 2 ⟨4, ([true]) ++ ((L)), ([true]) ++ (([true,true]) ++ ((R)))⟩ = some ⟨4, ([true]) ++ (([true,true]) ++ ((L))), ([true]) ++ ((R))⟩ := by rfl

theorem innerStep3 (n j : Nat) : run0 table (2*n) ⟨4, ([true,false,true,true]) ++ ((rep [true] j)), ([true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j))))⟩ = some ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))), ([true,false,true,true]) ++ ((rep [true] j))⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [true] [true,true] [true,true] 2 innerLocal3 n (([false,true,true]) ++ ((rep [true] j))) (([false,true,true]) ++ ((rep [true] j)))

theorem innerStep4 (n j : Nat) : run0 table 2 ⟨4, ([true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))), ([true,false,true,true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))), ([true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem innerRaw (n j : Nat) : run0 table (9+4*n) ⟨4, ([false,true,true,true,true]) ++ ((rep [true,true] n) ++ (([false,true]) ++ ((rep [true] j)))), ([true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true,true]) ++ ((rep [true,true] n) ++ (([false,true,true]) ++ ((rep [true] j)))), ([true,true]) ++ ((rep [true] j))⟩ := by

  have H := innerStep0 n j

  have H := join0 H (innerStep1 n j)

  have H := join0 H (innerStep2 n j)

  have H := join0 H (innerStep3 n j)

  have H := join0 H (innerStep4 n j)

  rw [show 2+2*n+5+2*n+2 = 9+4*n by omega] at H

  exact H

theorem finishStep0 (j : Nat) : run0 table 7 ⟨4, ([false,true,true,false,true]) ++ ((rep [true] j)), ([true]) ++ ((rep [true] j))⟩ = some ⟨4, ([true,true,true,true]) ++ ((rep [true] j)), ([true,true]) ++ ((rep [true] j))⟩ := by rfl

theorem finishLocal1 (L R : List Bool) : run0 table 1 ⟨4, ([true]) ++ ((L)), ([true,true]) ++ (([true]) ++ ((R)))⟩ = some ⟨4, ([true]) ++ (([true]) ++ ((L))), ([true,true]) ++ ((R))⟩ := by rfl

theorem finishStep1 (j : Nat) : run0 table (1*j) ⟨4, ([true,true,true,true]) ++ ((rep [true] j)), ([true,true]) ++ ((rep [true] j))⟩ = some ⟨4, ([true]) ++ ((rep [true] j) ++ (([true,true,true]) ++ ((rep [true] j)))), ([true,true])⟩ := by
  simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using sweepR table 4 [true] [true,true] [true] [true] 1 finishLocal1 j (([true,true,true]) ++ ((rep [true] j))) ([])

theorem finishStep2 (j : Nat) : run0 table 3 ⟨4, ([true]) ++ ((rep [true] j) ++ (([true,true,true]) ++ ((rep [true] j)))), ([true,true])⟩ = some ⟨4, ([false,true,true,true]) ++ ((rep [true] j) ++ (([true,true,true]) ++ ((rep [true] j)))), []⟩ := by rfl

theorem finishEqL (j : Nat) : (([false,true,true,true]) ++ ((rep [true] j) ++ (([true,true,true]) ++ ((rep [true] j))))) = (([false,true,true,true,true,true,true]) ++ ((rep [true,true] j))) := by
  change ((List.replicate 1 false) ++ ((List.replicate 3 true) ++ ((rep (List.replicate 1 true) j) ++ ((List.replicate 3 true) ++ ((rep (List.replicate 1 true) j)))))) = ((List.replicate 1 false) ++ ((List.replicate 6 true) ++ ((rep (List.replicate 2 true) j))))
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)

theorem finishRaw (j : Nat) : run0 table (10+1*j) ⟨4, ([false,true,true,false,true]) ++ ((rep [true] j)), ([true]) ++ ((rep [true] j))⟩ = some ⟨4, ([false,true,true,true,true,true,true]) ++ ((rep [true,true] j)), []⟩ := by

  have H := finishStep0 j

  have H := join0 H (finishStep1 j)

  have H := join0 H (finishStep2 j)

  rw [show 7+1*j+3 = 10+1*j by omega] at H

  rw [finishEqL j] at H

  exact H

theorem first (n : Nat) : run0 table (9+4*n) (family n) = some (middle n 0) := by
  simpa only [family,middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using firstRaw n

theorem inner (n j : Nat) : run0 table (9+4*n) (middle (n+1) j) = some (middle n (j+1)) := by
  simpa only [middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using innerRaw n j

theorem finish (j : Nat) : run0 table (10+j) (middle 0 j) = some (family (j+1)) := by
  simpa only [family,middle,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append,Nat.one_mul] using finishRaw j

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (cost 9 9 10 n) (family n) = some (family (n+1)) :=
  growthAll table 9 9 10 first inner finish n


theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (cost 9 9 10) entry (by intro n; unfold cost; omega) growth m hm
#print axioms never

#print axioms growth
end M9755
end BB6.Agent11Raw121Quadratic
