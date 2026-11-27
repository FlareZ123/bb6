import SweepPumping

open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw421LB.Leaf18612

def p : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨true,true,0⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨true,false,1⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true) => some (some ⟨true,true,4⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨false,false,1⟩)
  | (4,false) => some (some ⟨false,true,0⟩)
  | (4,true) => some (some ⟨false,true,5⟩)
  | (5,true) => some (some ⟨false,true,3⟩)
  | _ => none

def ones := rep [true]
def cfg (a b c : Nat) : Z0 := ⟨3,[false,false] ++ ones a ++ [false] ++ ones b,ones c⟩

theorem leftOne (L R : List Bool) :
    run0 p 1 ⟨1,[] ++ [true] ++ L,[] ++ R⟩ =
      some ⟨1,[] ++ L,[] ++ [true] ++ R⟩ := by rfl

theorem rightD (L R : List Bool) :
    run0 p 3 ⟨3,[true,false] ++ L,[] ++ [true] ++ R⟩ =
      some ⟨3,[true,false] ++ [true] ++ L,[] ++ R⟩ := by rfl

theorem rightA (L R : List Bool) :
    run0 p 1 ⟨0,[true] ++ L,[] ++ [true] ++ R⟩ =
      some ⟨0,[true] ++ [true] ++ L,[] ++ R⟩ := by rfl

theorem beginRed (n : Nat) (L R : List Bool) :
    run0 p 3 ⟨3,[false,false] ++ ones (n+5) ++ [false] ++ L,R⟩ =
      some ⟨1,ones n ++ [true,true,true,true,false] ++ L,[false,true,true] ++ R⟩ := by
  have h : run0 p 3 ⟨3,[false,false] ++ [true] ++ ones n ++ [true,true,true,true,false] ++ L,R⟩ =
      some ⟨1,ones n ++ [true,true,true,true,false] ++ L,[false,true,true] ++ R⟩ := by rfl
  have e : ones (n+5) = [true] ++ ones n ++ [true,true,true,true] := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [ones,rep,List.append_assoc,List.cons_append,List.nil_append] at ih ⊢
                   exact congrArg (List.cons true) ih
  rw [e]; simpa only [List.append_assoc] using h

theorem turnRed (L R : List Bool) :
    run0 p 8 ⟨1,[true,true,true,true,false] ++ L,R⟩ =
      some ⟨3,[true,false,false,true,true] ++ L,R⟩ := by rfl

theorem turnZero (R : List Bool) :
    run0 p 8 ⟨1,[true,true,true,true],R⟩ =
      some ⟨3,[true,false,false,true,true],R⟩ := by rfl

theorem finishD (L R : List Bool) :
    run0 p 3 ⟨3,[true,false] ++ L,[false] ++ R⟩ =
      some ⟨3,[false,false,true] ++ L,R⟩ := by rfl

theorem redTail (t : Nat) (L R : List Bool) :
    run0 p (4*t+10) ⟨3,[false,false] ++ ones (t+4) ++ [false] ++ L,R⟩ =
      some ⟨3,[false,false] ++ ones t ++ [false,true,true] ++ L,[true,true] ++ R⟩ := by
  cases t with
  | zero => rfl
  | succ n =>
    have h0 := beginRed n L R
    have h1 := sweepL p 1 [] [] [true] [true] 1 leftOne n ([true,true,true,true,false] ++ L) ([false,true,true] ++ R)
    have h2 := turnRed L (ones n ++ [false,true,true] ++ R)
    have h3 := sweepR p 3 [true,false] [] [true] [true] 3 rightD n ([false,true,true] ++ L) ([false,true,true] ++ R)
    have h4 := finishD (ones n ++ [false,true,true] ++ L) ([true,true] ++ R)
    simp only [ones,Nat.one_mul,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] at h0 h1 h2 h3 h4
    have h := join0 (join0 (join0 (join0 h0 h1) h2) h3) h4
    rw [show 3+n+8+3*n+3=4*(n+1)+10 by omega] at h
    simpa only [ones,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append,show n+1+4=n+5 by omega] using h

theorem beginZero (n : Nat) (R : List Bool) :
    run0 p 4 ⟨3,[false,false,false] ++ ones (n+5),R⟩ =
      some ⟨1,ones n ++ [true,true,true,true],[false,true,true,true] ++ R⟩ := by
  have h : run0 p 4 ⟨3,[false,false,false] ++ [true] ++ ones n ++ [true,true,true,true],R⟩ =
      some ⟨1,ones n ++ [true,true,true,true],[false,true,true,true] ++ R⟩ := by rfl
  have e : ones (n+5) = [true] ++ ones n ++ [true,true,true,true] := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [ones,rep,List.append_assoc,List.cons_append,List.nil_append] at ih ⊢
                   exact congrArg (List.cons true) ih
  rw [e]; simpa only [List.append_assoc] using h

theorem zeroTail (t : Nat) (R : List Bool) :
    run0 p (4*t+11) ⟨3,[false,false,false] ++ ones (t+4),R⟩ =
      some ⟨3,[false,false] ++ ones t ++ [false,true,true],[true,true,true] ++ R⟩ := by
  cases t with
  | zero => rfl
  | succ n =>
    have h0 := beginZero n R
    have h1 := sweepL p 1 [] [] [true] [true] 1 leftOne n [true,true,true,true] ([false,true,true,true] ++ R)
    have h2 := turnZero (ones n ++ [false,true,true,true] ++ R)
    have h3 := sweepR p 3 [true,false] [] [true] [true] 3 rightD n [false,true,true] ([false,true,true,true] ++ R)
    have h4 := finishD (ones n ++ [false,true,true]) ([true,true,true] ++ R)
    simp only [ones,Nat.one_mul,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] at h0 h1 h2 h3 h4
    have h := join0 (join0 (join0 (join0 h0 h1) h2) h3) h4
    rw [show 4+n+8+3*n+3=4*(n+1)+11 by omega] at h
    simpa only [ones,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append,show n+1+4=n+5 by omega] using h

theorem beginExit (c : Nat) (L : List Bool) :
    run0 p 7 ⟨3,[false,false,true,true,false] ++ L,ones c⟩ =
      some ⟨0,[true,false,true,true] ++ L,ones (c+1)⟩ := by rfl

theorem finishExit (L : List Bool) :
    run0 p 4 ⟨0,[true] ++ L,[]⟩ =
      some ⟨3,[false,false,true,true,true] ++ L,[]⟩ := by rfl

theorem exitTail (c : Nat) (L : List Bool) :
    run0 p (c+12) ⟨3,[false,false,true,true,false] ++ L,ones c⟩ =
      some ⟨3,[false,false] ++ ones (c+4) ++ [false,true,true] ++ L,[]⟩ := by
  have h0 := beginExit c L
  have h1 := sweepR p 0 [true] [] [true] [true] 1 rightA (c+1) ([false,true,true] ++ L) []
  have h2 := finishExit (ones (c+1) ++ [false,true,true] ++ L)
  -- The final fixed sweep contributes three extra ones after the saved leading one.
  simp only [ones,Nat.one_mul,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] at h0 h1 h2
  have h := join0 (join0 h0 h1) h2
  rw [show 7+(c+1)+4=c+12 by omega] at h
  simpa only [ones,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h

theorem reduce (a b c : Nat) :
    run0 p (4*a+10) (cfg (a+4) b c) = some (cfg a (b+2) (c+2)) := by
  simpa only [cfg,ones,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using redTail a (ones b) (ones c)

theorem swapZero (b c : Nat) :
    run0 p (4*b+11) (cfg 0 (b+4) c) = some (cfg b 2 (c+3)) := by
  simpa only [cfg,ones,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using zeroTail b (ones c)

theorem exitTwo (b c : Nat) :
    run0 p (c+12) (cfg 2 b c) = some (cfg (c+4) (b+2) 0) := by
  simpa only [cfg,ones,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using exitTail c (ones b)

def redCost (a : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => (4*(a+4*k)+10) + redCost a k

theorem reduceMany (a k b c : Nat) :
    run0 p (redCost a k) (cfg (a+4*k) b c) = some (cfg a (b+2*k) (c+2*k)) := by
  induction k generalizing b c with
  | zero => simp [redCost,run0]
  | succ k ih =>
    have h := join0 (reduce (a+4*k) b c) (ih (b+2) (c+2))
    simpa only [redCost,show a+4*(k+1)=a+4*k+4 by omega,
      show b+2+2*k=b+2*(k+1) by omega,show c+2+2*k=c+2*(k+1) by omega] using h

def family (n : Nat) : Z0 := cfg (8*n+10) (2*n+2) 0

def cost (n : Nat) : Nat :=
    redCost 2 (2*n+2) + (4*n+4+12) +
    redCost 0 (n+2) + (4*(8*n+8)+11) +
    redCost 0 (2*n+2) + (4*(4*n+2)+11) +
    redCost 2 n + (8*n+14+12)

theorem first : run0 p 55 ⟨0,[],[]⟩ = some (family 0) := by decide

theorem grow (n : Nat) : run0 p (cost n) (family n) = some (family (n+1)) := by
  have h0 : run0 p (redCost 2 (2*n+2)) (family n) = some (cfg 2 (6*n+6) (4*n+4)) := by
    simpa only [family,show 2+4*(2*n+2)=8*n+10 by omega,
      show 2*n+2+2*(2*n+2)=6*n+6 by omega,show 0+2*(2*n+2)=4*n+4 by omega] using reduceMany 2 (2*n+2) (2*n+2) 0
  have h1 : run0 p (4*n+4+12) (cfg 2 (6*n+6) (4*n+4)) = some (cfg (4*n+8) (6*n+8) 0) := by
    simpa only [show 4*n+4+4=4*n+8 by omega,show 6*n+6+2=6*n+8 by omega] using exitTwo (6*n+6) (4*n+4)
  have h2 : run0 p (redCost 0 (n+2)) (cfg (4*n+8) (6*n+8) 0) = some (cfg 0 (8*n+12) (2*n+4)) := by
    simpa only [show 0+4*(n+2)=4*n+8 by omega,show 6*n+8+2*(n+2)=8*n+12 by omega,
      show 0+2*(n+2)=2*n+4 by omega] using reduceMany 0 (n+2) (6*n+8) 0
  have h3 : run0 p (4*(8*n+8)+11) (cfg 0 (8*n+12) (2*n+4)) = some (cfg (8*n+8) 2 (2*n+7)) := by
    simpa only [show 8*n+8+4=8*n+12 by omega,show 2*n+4+3=2*n+7 by omega] using swapZero (8*n+8) (2*n+4)
  have h4 : run0 p (redCost 0 (2*n+2)) (cfg (8*n+8) 2 (2*n+7)) = some (cfg 0 (4*n+6) (6*n+11)) := by
    simpa only [show 0+4*(2*n+2)=8*n+8 by omega,show 2+2*(2*n+2)=4*n+6 by omega,
      show 2*n+7+2*(2*n+2)=6*n+11 by omega] using reduceMany 0 (2*n+2) 2 (2*n+7)
  have h5 : run0 p (4*(4*n+2)+11) (cfg 0 (4*n+6) (6*n+11)) = some (cfg (4*n+2) 2 (6*n+14)) := by
    simpa only [show 4*n+2+4=4*n+6 by omega,show 6*n+11+3=6*n+14 by omega] using swapZero (4*n+2) (6*n+11)
  have h6 : run0 p (redCost 2 n) (cfg (4*n+2) 2 (6*n+14)) = some (cfg 2 (2*n+2) (8*n+14)) := by
    simpa only [show 2+4*n=4*n+2 by omega,show 2+2*n=2*n+2 by omega,show 6*n+14+2*n=8*n+14 by omega] using reduceMany 2 n 2 (6*n+14)
  have h7 : run0 p (8*n+14+12) (cfg 2 (2*n+2) (8*n+14)) = some (family (n+1)) := by
    simpa only [family,show 8*n+14+4=8*(n+1)+10 by omega,show 2*n+2+2=2*(n+1)+2 by omega] using exitTwo (2*n+2) (8*n+14)
  exact join0 (join0 (join0 (join0 (join0 (join0 (join0 h0 h1) h2) h3) h4) h5) h6) h7

theorem live : ∀ m, compatible p m → NeverHalts m :=
  never_of_growth p family 55 cost first (by intro n; unfold cost; omega) grow

#print axioms live
end BB6.Agent32Raw421LB.Leaf18612
