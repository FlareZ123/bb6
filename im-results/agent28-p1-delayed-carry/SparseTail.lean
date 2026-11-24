import ScalarTail
namespace BB6.Agent28SparseTail
open BB6.Agent28BitCarry BB6.Agent28BitSpread BB6.Agent28BitGroup BB6.Agent28ScalarTail BB6.Agent45.DelayedCarry

theorem spreadStep_or (L k x y : Nat) : spreadStep L k (x|||y)=spreadStep L k x ||| spreadStep L k y := by
  apply Nat.eq_of_testBit_eq
  intro p
  simp only [spreadStep,Nat.testBit_and,Nat.testBit_or,Nat.testBit_shiftLeft]
  cases (decide (p≥2^k)) <;> cases x.testBit p <;> cases y.testBit p <;>
    cases x.testBit (p-2^k) <;> cases y.testBit (p-2^k) <;>
    cases (laneMask (2^k) (L-k)).testBit p <;> rfl

theorem spreadFrom_or (L k x y : Nat) : spreadFrom L k (x|||y)=spreadFrom L k x ||| spreadFrom L k y := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih => simp only [spreadFrom,spreadStep_or,ih]

theorem reverseStep_or (L C t x y : Nat) : reverseStep L C t (x|||y)=reverseStep L C t x ||| reverseStep L C t y := by
  apply Nat.eq_of_testBit_eq
  intro p
  simp only [reverseStep,spreadEven,spreadFrom_or,Nat.testBit_and,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_shiftRight]
  cases (decide (p≥t)) <;> cases (decide (C+p≥t)) <;>
    cases (spreadFrom L L x).testBit (p-t) <;> cases (spreadFrom L L y).testBit (p-t) <;>
    cases (spreadFrom L L x).testBit (C+p-t) <;> cases (spreadFrom L L y).testBit (C+p-t) <;>
    cases (2^C-1).testBit p <;> rfl

theorem backRun_or (L n B s k x y : Nat) : backRun L n B s k (x|||y)=backRun L n B s k x ||| backRun L n B s k y := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih => simp only [backRun,reverseStep_or,ih]

def carryMask : List Nat → Nat
  | [] => 0
  | c::cs => 2^c ||| carryMask cs

def scalarMask (n B s k : Nat) : List Nat → Nat
  | [] => 0
  | c::cs => (scalarBack n B s k c).elim 0 (fun d=>2^d) ||| scalarMask n B s k cs

theorem backRun_sparse (L n B s k : Nat) (cs : List Nat) (hb : n+s+k+2<2^L)
    (hc : ∀ c∈cs, c<2^L) : backRun L n B s k (carryMask cs)=scalarMask n B s k cs := by
  induction cs with
  | nil => exact backRun_zero L n B s k
  | cons c cs ih =>
    simp only [carryMask,scalarMask,backRun_or]
    rw [backRun_scalar L n B s k c (hc c (List.mem_cons_self ..)) hb]
    rw [ih (fun d hd=>hc d (List.mem_cons_of_mem c hd))]

theorem backRun_sparseTail (L n B s k j bits out : Nat) (cs : List Nat)
    (hb : n+s+k+2<2^L) (hc : ∀ c∈cs, c<2^L)
    (h1 : backRun L n B (s+k) j bits=carryMask cs)
    (h2 : scalarMask n B s k cs=out) : backRun L n B s (k+j) bits=out := by
  rw [backRun_add,h1,backRun_sparse L n B s k cs hb hc,h2]

#print axioms backRun_sparseTail
end BB6.Agent28SparseTail
