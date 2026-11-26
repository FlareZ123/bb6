import SweepPumping

namespace BB6Coverage.Agent31Pump.D3
open BB6Coverage Agent31Pump
set_option maxHeartbeats 0

def p : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨false,true,1⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | _,_ => none

def A (L R : List Bool) : Z0 := ⟨0,L,R⟩
def B (L R : List Bool) : Z0 := ⟨1,L,R⟩
def P (k : Nat) : List Bool := rep [true,false] k ++ [true,true]

theorem t (L R : List Bool) : run0 p 2 (A (true::false::L) R) = some (A L (true::false::R)) := by rfl
theorem j (L R : List Bool) : run0 p 7 (A (true::true::false::L) R) = some (A L (true::false::true::R)) := by rfl
theorem g (L R : List Bool) : run0 p 3 (A (true::true::true::L) R) = some (A (false::false::L) (false::R)) := by rfl
theorem z (L R : List Bool) : run0 p 3 (A (false::L) (false::false::R)) = some (A (true::true::L) (true::R)) := by rfl
theorem z1 (L R : List Bool) : run0 p 4 (A (false::L) (false::true::R)) = some (A (false::false::true::L) R) := by rfl

theorem shiftT (k : Nat) (L R : List Bool) :
    run0 p (2*k) (A (rep [true,false] k ++ L) R) = some (A L (rep [true,false] k ++ R)) := by
  simpa [A] using sweepL p 0 [] [] [true,false] [true,false] 2 t k L R

theorem shiftZ (k : Nat) (L R : List Bool) :
    run0 p (4*k) (A (false::L) (rep [false,true] k ++ R)) = some (A (false::(rep [false,true] k ++ L)) R) := by
  simpa [A] using sweepR p 0 [false] [] [false,true] [false,true] 4 z1 k L R

theorem bOne (L R : List Bool) : run0 p 2 (B (true::L) (false::true::R)) = some (B (true::true::true::L) R) := by rfl
theorem bShift (k : Nat) (L R : List Bool) :
    run0 p (2*k) (B (true::L) (rep [false,true] k ++ R)) = some (B (true::(rep [true,true] k ++ L)) R) := by
  simpa [B] using sweepR p 1 [true] [] [false,true] [true,true] 2 bOne k L R

theorem rep_add (b : List Bool) (n m : Nat) : rep b (n+m) = rep b n ++ rep b m := by
  induction n with
  | zero => simp [rep]
  | succ n ih => rw [show n+1+m=n+m+1 by omega]; simp [rep,ih,List.append_assoc]

theorem pure_rotate (k : Nat) : P k = true::(rep [false,true] k ++ [true]) := by
  have h := rotate true [false] k
  have hh := congrArg (fun l => l ++ [true]) h
  simpa [P,List.append_assoc] using hh.symm

theorem rep11_one (k : Nat) (L : List Bool) : rep [true,true] k ++ true::L = true::(rep [true,true] k ++ L) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [rep,ih]

theorem rep01_zero (k : Nat) (L : List Bool) : rep [false,true] k ++ false::L = false::(rep [true,false] k ++ L) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [rep,ih]

theorem pureP (k : Nat) (L : List Bool) :
    run0 p (2*k+34) (A (false::L) (P k)) = some (A (true::(rep [true,true] k ++ L)) (P 3)) := by
  have h0 : run0 p 1 (A (false::L) (P k)) = some (B (true::true::L) (rep [false,true] k ++ [true])) := by
    rw [pure_rotate]; rfl
  have h := join0 h0 (bShift k (true::L) [true])
  rw [rep11_one] at h
  have fin (X : List Bool) : run0 p 33 (B (true::true::X) [true]) = some (A (true::X) (P 3)) := by rfl
  have H := join0 h (fin (rep [true,true] k ++ L))
  rw [show 1+2*k+33=2*k+34 by omega] at H
  exact H

theorem pureG (k : Nat) (L : List Bool) :
    run0 p (6*k+35) (A (true::true::true::L) (P k)) = some (A L (P (k+4))) := by
  have h := g L (P k)
  have hr : false::P k = rep [false,true] (k+1) ++ [true] := by rw [pure_rotate]; rfl
  rw [hr] at h
  have H := join0 h (shiftZ (k+1) (false::L) [true])
  have post (X : List Bool) : run0 p 20 (A (false::false::true::X) [true]) = some (A (true::false::true::false::true::false::true::X) [true,true]) := by rfl
  have H' := join0 H (post (rep [false,true] k ++ false::L))
  rw [rep01_zero] at H'
  have H'' : run0 p (3+4*(k+1)+20) (A (true::true::true::L) (P k)) = some (A (rep [true,false] (k+4) ++ L) [true,true]) := by
    simpa [rep_add,show k+4=4+k by omega,rep,List.append_assoc] using H'
  have J := join0 H'' (shiftT (k+4) L [true,true])
  rw [show 3+4*(k+1)+20+2*(k+4)=6*k+35 by omega] at J
  exact J

#print axioms pureP
#print axioms pureG
#print axioms shiftT
#print axioms shiftZ
end BB6Coverage.Agent31Pump.D3
