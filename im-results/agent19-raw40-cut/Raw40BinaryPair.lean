import Agent46AutoPump
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.BinaryPair
open BB6Coverage BB6Coverage.Agent31Pump

def table (b : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨false,true,if b then 1 else 0⟩)
  | _,_ => none

def digit (b v : Bool) : List Bool :=
  if v then (if b then [false,false,true] else [true,false,false]) else [false,false,false]
def enc (b : Bool) (xs : List Bool) := xs.flatMap (digit b)
def inc : List Bool → List Bool
  | [] => [false]
  | false::xs => true::xs
  | true::xs => false::inc xs

def C (b : Bool) (xs : List Bool) : Z0 :=
  ⟨5,[false,false],rep [false] (if b then 3 else 6) ++ enc b xs ++ [true]⟩
def K (b : Bool) (k : Nat) (xs : List Bool) : Z0 :=
  ⟨1,rep [true] (3*k+(if b then 4 else 5)) ++ [false],
    rep [false] (if b then 0 else 2) ++ enc b xs ++ [true]⟩
def E (n : Nat) (R : List Bool) : Z0 := ⟨4,rep [true] n ++ [false],R⟩

theorem rep_add (P : List Bool) (a b : Nat) : rep P (a+b) = rep P a ++ rep P b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [Nat.succ_add,rep,ih,rep]; simp only [List.append_assoc]

theorem enc_zeros (b : Bool) (k : Nat) : enc b (List.replicate k false) = rep [false] (3*k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ,enc,List.flatMap_cons,digit,Bool.false_eq_true,↓reduceIte]
    change [false,false,false] ++ enc b (List.replicate k false) = _
    rw [ih,show 3*(k+1)=3+3*k by omega,rep_add]
    rfl

theorem init (b : Bool) : run0 (table b) 31 ⟨0,[],[]⟩ = some (C b (if b then [false] else [])) := by cases b <;> rfl

theorem enter (b : Bool) (xs : List Bool) : run0 (table b) (if b then 9 else 14) (C b xs) = some (K b 0 xs) := by cases b <;> rfl

theorem advance (b : Bool) (k : Nat) (xs : List Bool) : run0 (table b) 5 (K b k (true::xs)) = some (K b (k+1) xs) := by
  cases b <;> rfl

theorem end_nil_A (k : Nat) : run0 (table false) 15 (K false k []) = some (E (3*k+10) [true]) := by rfl

theorem end_nil_B (k : Nat) : run0 (table true) 11 (K true k []) = some (E (3*k+7) [true]) := by rfl

theorem end_zero_A (k : Nat) (xs : List Bool) : run0 (table false) 10 (K false k (false::xs)) = some (E (3*k+7) ([true,false,false] ++ enc false xs ++ [true])) := by rfl

theorem end_zero_B (k : Nat) (xs : List Bool) : run0 (table true) 10 (K true k (false::xs)) = some (E (3*k+6) ([true] ++ enc true xs ++ [true])) := by rfl

theorem clear (b : Bool) (n : Nat) (R : List Bool) : run0 (table b) n (E n R) = some ⟨4,[false],rep [false] n ++ R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h : run0 (table b) 1 (E (n+1) R) = some (E n (false::R)) := by rfl
    have hh := join0 h (ih (false::R))
    rw [show 1+n=n+1 by omega] at hh
    have eq : rep [false] n ++ false::R = rep [false] (n+1) ++ R := by
      rw [rep, ← rep_snoc [false] n, List.append_assoc]; rfl
    rw [eq] at hh
    exact hh

theorem finish (b : Bool) (n : Nat) (R : List Bool) : run0 (table b) (n+2) (E (n+1) R) = some ⟨5,[false,false],rep [false] n ++ R⟩ := by
  have h : run0 (table b) 1 ⟨4,[false],rep [false] (n+1) ++ R⟩ = some ⟨5,[false,false],rep [false] n ++ R⟩ := by rfl
  have hh := join0 (clear b (n+1) R) h
  simpa only [Nat.add_assoc] using hh

def carryCost (b : Bool) : List Bool → Nat
  | [] => if b then 19 else 26
  | false::_ => if b then 17 else 18
  | true::xs => 8 + carryCost b xs

theorem enc_append (b : Bool) (xs ys : List Bool) : enc b (xs++ys) = enc b xs ++ enc b ys := by simp [enc]
theorem enc_cons (b x : Bool) (xs : List Bool) : enc b (x::xs) = digit b x ++ enc b xs := by rfl

theorem carry (b : Bool) (k : Nat) (xs : List Bool) : run0 (table b) (carryCost b xs + 3*k) (K b k xs) = some (C b (List.replicate k false ++ inc xs)) := by
  induction xs generalizing k with
  | nil =>
    cases b
    · have h := join0 (end_nil_A k) (finish false (3*k+9) [true])
      rw [show carryCost false [] +3*k=15+(3*k+9+2) by simp [carryCost]; omega, h]
      simp only [C,inc,enc_append,enc_zeros,ite_false,Bool.false_eq_true]
      have eq : rep [false] 6 ++ rep [false] (3*k) ++ rep [false] 3 = rep [false] (3*k+9) := by
        rw [← rep_add,← rep_add]; congr 1; omega
      change some (⟨5,[false,false],rep [false] (3*k+9) ++ [true]⟩ : Z0) = some ⟨5,[false,false],rep [false] 6 ++ (rep [false] (3*k) ++ rep [false] 3) ++ [true]⟩
      simp only [← List.append_assoc,eq]
    · have h := join0 (end_nil_B k) (finish true (3*k+6) [true])
      rw [show carryCost true [] +3*k=11+(3*k+6+2) by simp [carryCost]; omega,h]
      simp only [C,inc,enc_append,enc_zeros,ite_true]
      have eq : rep [false] 3 ++ rep [false] (3*k) ++ rep [false] 3 = rep [false] (3*k+6) := by
        rw [← rep_add,← rep_add]; congr 1; omega
      change some (⟨5,[false,false],rep [false] (3*k+6) ++ [true]⟩ : Z0) = some ⟨5,[false,false],rep [false] 3 ++ (rep [false] (3*k) ++ rep [false] 3) ++ [true]⟩
      simp only [← List.append_assoc,eq]
  | cons x xs ih =>
    cases x
    · cases b
      · have h := join0 (end_zero_A k xs) (finish false (3*k+6) ([true,false,false] ++ enc false xs ++ [true]))
        rw [show carryCost false (false::xs)+3*k=10+(3*k+6+2) by simp [carryCost]; omega,h]
        simp only [C,inc,enc_append,enc_zeros,enc_cons,digit,ite_true,ite_false,Bool.false_eq_true,List.append_assoc]
        rw [← List.append_assoc (rep [false] 6) (rep [false] (3*k)),← rep_add,show 6+3*k=3*k+6 by omega]
      · have h := join0 (end_zero_B k xs) (finish true (3*k+5) ([true] ++ enc true xs ++ [true]))
        rw [show carryCost true (false::xs)+3*k=10+(3*k+5+2) by simp [carryCost]; omega,h]
        simp only [C,inc,enc_append,enc_zeros,enc_cons,digit,ite_true,List.append_assoc]
        have eq : rep [false] 3 ++ rep [false] (3*k) ++ [false,false] = rep [false] (3*k+5) := by
          change rep [false] 3 ++ rep [false] (3*k) ++ rep [false] 2 = _
          rw [← rep_add,← rep_add]; congr 1; omega
        rw [show [false,false,true] = [false,false] ++ [true] by rfl]
        simp only [← List.append_assoc,eq]
    · have h := join0 (advance b k xs) (ih (k+1))
      rw [show carryCost b (true::xs)+3*k=5+(carryCost b xs+3*(k+1)) by simp [carryCost]; omega]
      have eq : List.replicate (k+1) false ++ inc xs = List.replicate k false ++ (false::inc xs) := by
        rw [← List.replicate_append_replicate (n:=k) (m:=1) (a:=false), List.append_assoc]; rfl
      simpa only [inc,eq] using h

def cost (b : Bool) (xs : List Bool) := (if b then 9 else 14) + carryCost b xs

theorem epoch (b : Bool) (xs : List Bool) : run0 (table b) (cost b xs) (C b xs) = some (C b (inc xs)) := by
  simpa [cost] using join0 (enter b xs) (carry b 0 xs)

def orbit (b : Bool) : Nat → List Bool
  | 0 => if b then [false] else []
  | k+1 => inc (orbit b k)

theorem never (b : Bool) (m : Machine) (hm : compatible (table b) m) : NeverHalts m := by
  apply never_of_growth (table b) (fun k => C b (orbit b k)) 31 (fun k => cost b (orbit b k)) (init b)
  · intro k; cases b <;> simp [cost] <;> omega
  · intro k; exact epoch b (orbit b k)
  · exact hm

namespace Leaf486
abbrev table := BinaryPair.table false
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BinaryPair.never false m hm
end Leaf486
namespace Leaf487
abbrev table := BinaryPair.table true
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BinaryPair.never true m hm
end Leaf487

#print axioms epoch
#print axioms never
end BB6.Agent19Raw40.BinaryPair
