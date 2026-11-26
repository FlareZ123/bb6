import SweepPumping

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace BB6.Agent2Raw124OneLB2083
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  ([some (some ⟨true,true,1⟩), some (some ⟨false,false,0⟩),
    some (some ⟨true,true,2⟩), some (some ⟨true,false,4⟩),
    some (some ⟨false,true,3⟩), some (some ⟨false,true,0⟩),
    some (some ⟨true,false,3⟩), some (some ⟨true,true,4⟩),
    some (some ⟨true,false,2⟩), some (some ⟨true,false,5⟩),
    none, some (some ⟨true,false,1⟩)] : List (Option Transition))[2*s.1.val+s.2.toNat]?.getD none

private def ones (n : Nat) : List Bool := List.replicate n true
private def B (n m : Nat) : Z0 := ⟨1,ones n,ones m⟩
private def C (n m : Nat) : Z0 := ⟨2,ones n,ones m⟩

private theorem ones_add (a b : Nat) : ones a ++ ones b = ones (a+b) := by
  simp only [ones,List.replicate_append_replicate]

private theorem rightOne (L R : List Bool) :
    run0 table 4 ⟨2,[true]++L,[true,true]++R⟩ =
    some ⟨2,[true]++[true,true]++L,R⟩ := by rfl
private theorem leftOne (L R : List Bool) :
    run0 table 3 ⟨1,[true,true,true]++L,R⟩ =
    some ⟨1,L,[true,true,true]++R⟩ := by rfl

private theorem repOnes (a n : Nat) : rep (ones a) n = ones (a*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rep,ih,ones_add,Nat.mul_succ,Nat.add_comm]

private theorem rightSweep (a b n : Nat) :
    run0 table (4*n) (C (a+1) (2*n+b)) = some (C (2*n+a+1) b) := by
  have h := sweepR table 2 [true] [] [true,true] [true,true] 4
    (fun L R => rightOne L R) n (ones a) (ones b)
  change run0 table (4*n) ⟨2,ones 1++ones a,[]++rep (ones 2) n++ones b⟩ =
    some ⟨2,ones 1++rep (ones 2) n++ones a,[]++ones b⟩ at h
  simp only [List.nil_append,repOnes,ones_add] at h
  unfold C
  rw [show a+1=1+a by omega,show 2*n+a+1=1+2*n+a by omega]
  exact h

private theorem leftSweep (a b n : Nat) :
    run0 table (3*n) (B (3*n+a) b) = some (B a (3*n+b)) := by
  have h := sweepL table 1 [] [] [true,true,true] [true,true,true] 3
    (fun L R => leftOne L R) n (ones a) (ones b)
  change run0 table (3*n) ⟨1,[]++rep (ones 3) n++ones a,[]++ones b⟩ =
    some ⟨1,[]++ones a,[]++rep (ones 3) n++ones b⟩ at h
  simpa only [List.nil_append,repOnes,ones_add,B] using h

private theorem cStart (n : Nat) :
    run0 table 5 (C 0 (n+3)) = some (C 2 (n+2)) := by rfl
private theorem bStart (n : Nat) :
    run0 table 1 (B 0 (n+1)) = some (C 2 n) := by rfl
private theorem turnEven (n : Nat) :
    run0 table 11 (C (n+2) 0) = some (C (n+1) 5) := by rfl
private theorem turnOdd (n : Nat) :
    run0 table 10 (C (n+2) 1) = some (B (n+2) 3) := by rfl
private theorem endC (n : Nat) :
    run0 table 2 (B 1 n) = some (C 0 (n+2)) := by rfl

private theorem evenTurn (n : Nat) :
    run0 table 29 (C (n+2) 0) = some (B (n+5) 3) := by
  have h := join0 (turnEven n) (rightSweep n 1 2)
  rw [show 2*2+n+1=n+3+2 by omega] at h
  exact join0 h (turnOdd (n+3))

private theorem phase1 (k : Nat) :
    run0 table (54*k+51) (C 0 (18*k+5)) = some (B 0 (18*k+12)) := by
  have h0 := cStart (18*k+2)
  have h1 := rightSweep 1 0 (9*k+2)
  rw [show 2*(9*k+2)+0=18*k+2+2 by omega,
      show 2*(9*k+2)+1+1=18*k+4+2 by omega] at h1
  have h := join0 (join0 h0 h1) (evenTurn (18*k+4))
  have h2 := leftSweep 0 3 (6*k+3)
  rw [show 3*(6*k+3)+0=18*k+4+5 by omega,
      show 3*(6*k+3)+3=18*k+12 by omega] at h2
  have hh := join0 h h2
  rw [show 18*k+2+3=18*k+5 by omega,
      show 5+4*(9*k+2)+29+3*(6*k+3)=54*k+51 by omega] at hh
  exact hh

private theorem phase2 (k : Nat) :
    run0 table (54*k+43) (B 0 (18*k+12)) = some (B 0 (18*k+15)) := by
  have h1 := rightSweep 1 1 (9*k+5)
  rw [show 2*(9*k+5)+1=18*k+11 by omega,
      show 18*k+11+1=18*k+10+2 by omega] at h1
  have h := join0 (join0 (bStart (18*k+11)) h1) (turnOdd (18*k+10))
  have h2 := leftSweep 0 3 (6*k+4)
  rw [show 3*(6*k+4)+0=18*k+10+2 by omega,
      show 3*(6*k+4)+3=18*k+15 by omega] at h2
  have hh := join0 h h2
  rw [show 18*k+11+1=18*k+12 by omega,
      show 1+4*(9*k+5)+10+3*(6*k+4)=54*k+43 by omega] at hh
  exact hh

private theorem phase3 (k : Nat) :
    run0 table (54*k+78) (B 0 (18*k+15)) = some (C 0 (18*k+23)) := by
  have h1 := rightSweep 1 0 (9*k+7)
  rw [show 2*(9*k+7)+0=18*k+14 by omega,
      show 2*(9*k+7)+1+1=18*k+14+2 by omega] at h1
  have h := join0 (join0 (bStart (18*k+14)) h1) (evenTurn (18*k+14))
  have h2 := leftSweep 1 3 (6*k+6)
  rw [show 3*(6*k+6)+1=18*k+14+5 by omega,
      show 3*(6*k+6)+3=18*k+21 by omega] at h2
  have hh := join0 (join0 h h2) (endC (18*k+21))
  rw [show 18*k+14+1=18*k+15 by omega,
      show 18*k+21+2=18*k+23 by omega,
      show 1+4*(9*k+7)+29+3*(6*k+6)+2=54*k+78 by omega] at hh
  exact hh

def family (k : Nat) : Z0 := C 0 (18*k+5)
def cost (k : Nat) : Nat := 162*k+172

theorem root : run0 table 10 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (k : Nat) : run0 table (cost k) (family k) = some (family (k+1)) := by
  have h := join0 (join0 (phase1 k) (phase2 k)) (phase3 k)
  unfold cost family
  rw [show 162*k+172=(54*k+51)+(54*k+43)+(54*k+78) by omega,
    show 18*(k+1)+5=18*k+23 by omega]
  exact h

theorem never_source (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 10 cost root (by intro k; unfold cost; omega) growth m hm

#print axioms growth
#print axioms root
#print axioms never_source
end BB6.Agent2Raw124OneLB2083
