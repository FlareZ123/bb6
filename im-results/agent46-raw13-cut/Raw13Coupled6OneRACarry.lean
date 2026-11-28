import SweepPumping

namespace BB6Coverage.Agent31Pump.Raw13Coupled6OneRACarry
open BB6Coverage Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def p : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,1⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,2⟩)
  | 3,true => some (some ⟨false,false,0⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨false,false,2⟩)
  | _,_ => none

def A (L R : List Bool) : Z0 := ⟨0,L,R⟩
def B (L R : List Bool) : Z0 := ⟨1,L,R⟩
def one : List Bool := [true]
def zero : List Bool := [false]
def d0 : List Bool := [false,true,false,true]
def d1 : List Bool := [false,true,true,false]
def pair : List Bool := [false,true]

theorem b_shift (L R : List Bool) :
    run0 p 1 (B (true::L) (true::R)) = some (B (true::false::L) R) := by rfl

theorem b_sweep (n : Nat) (L R : List Bool) :
    run0 p n (B (true::L) (rep one n ++ R)) = some (B (true::(rep zero n ++ L)) R) := by
  simpa [B,one,zero] using sweepR p 1 [true] [] [true] [false] 1 b_shift n L R

theorem b_scan (k : Nat) (L R : List Bool) (b : Bool) :
    run0 p k (B ((rep one k ++ b::R).headD false::L) (rep one k ++ b::R).tail) =
    some (B (b::(rep zero k ++ L)) R) := by
  cases k with
  | zero => rfl
  | succ k =>
    have h := b_sweep k L (b::R)
    have f (X : List Bool) : run0 p 1 (B (true::X) (b::R)) = some (B (b::false::X) R) := by rfl
    have H := join0 h (f (rep zero k ++ L))
    simpa [rep,one,zero] using H

theorem start_scan (k : Nat) (L R : List Bool) (b : Bool) :
    run0 p (k+1) (A (false::L) (rep one k ++ b::R)) =
      some (B (b::(rep zero k ++ true::L)) R) := by
  have h : run0 p 1 (A (false::L) (rep one k ++ b::R)) =
      some (B ((rep one k ++ b::R).headD false::true::L) (rep one k ++ b::R).tail) := by rfl
  have H := join0 h (b_scan k (true::L) R b)
  simpa [Nat.add_comm] using H

theorem step_zero (k : Nat) (L R : List Bool) :
    run0 p (k+3) (A (false::L) (rep one k ++ false::false::R)) =
      some (A (true::(rep zero k ++ true::L)) (true::R)) := by
  have h := start_scan k L (false::R) false
  have f (X : List Bool) : run0 p 2 (B (false::X) (false::R)) = some (A (true::X) (true::R)) := by rfl
  have H := join0 h (f (rep zero k ++ true::L))
  simpa only [Nat.add_assoc] using H

theorem step_alt (k : Nat) (L R : List Bool) :
    run0 p (k+6) (A (false::L) (rep one k ++ d0 ++ R)) =
      some (A (true::true::(rep zero k ++ true::L)) (true::false::R)) := by
  have h := start_scan k L (true::false::true::R) false
  have f (X : List Bool) : run0 p 5 (B (false::X) (true::false::true::R)) = some (A (true::true::X) (true::false::R)) := by rfl
  have H := join0 h (f (rep zero k ++ true::L))
  simpa [d0,Nat.add_assoc] using H

theorem step_double (k : Nat) (L R : List Bool) (s : Bool) :
    run0 p (k+4) (A (false::L) (rep one k ++ false::true::true::s::R)) =
      some (A (s::true::true::true::(rep zero k ++ true::L)) R) := by
  have h := start_scan k L (true::true::s::R) false
  have f (X : List Bool) : run0 p 3 (B (false::X) (true::true::s::R)) = some (A (s::true::true::true::X) R) := by rfl
  have H := join0 h (f (rep zero k ++ true::L))
  simpa only [Nat.add_assoc] using H

theorem left_pair (L R : List Bool) : run0 p 2 (A (true::true::L) R) = some (A L (false::true::R)) := by rfl

theorem left_triple (L R : List Bool) : run0 p 3 (A (true::false::false::L) R) = some (A L (true::true::true::R)) := by rfl

theorem left_flip (L R : List Bool) : run0 p 4 (A (true::false::true::L) R) = some (A (true::true::true::L) R) := by rfl

theorem rep_add' (b : List Bool) (n m : Nat) : rep b (n+m) = rep b n ++ rep b m := by
  induction n with
  | zero => simp [rep]
  | succ n ih => rw [show n+1+m=n+m+1 by omega]; simp [rep,ih,List.append_assoc]

theorem d1_scan (j : Nat) (L R : List Bool) :
    run0 p (4*j) (A (false::L) (rep d1 j ++ R)) = some (A (false::(rep [true,true,true,true] j ++ L)) R) := by
  have h (X Y : List Bool) : run0 p 4 (A (false::X) (d1 ++ Y)) = some (A (false::true::true::true::true::X) Y) := by rfl
  simpa [A] using sweepR p 0 [false] [] d1 [true,true,true,true] 4 h j L R

theorem rep11_double (j : Nat) : rep [true,true] (2*j) = rep [true,true,true,true] j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [show 2*(j+1)=2+2*j by omega,rep_add',ih]; rfl

theorem pair_double (j : Nat) : rep pair (2*j) = rep d0 j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [show 2*(j+1)=2+2*j by omega,rep_add',ih]; rfl

theorem left_pairs (n : Nat) (L R : List Bool) :
    run0 p (2*n) (A (rep [true,true] n ++ L) R) = some (A L (rep pair n ++ R)) := by
  simpa [A,pair] using sweepL p 0 [] [] [true,true] [false,true] 2 left_pair n L R

theorem carry0 (j : Nat) (L R : List Bool) :
    run0 p (8*j+8) (A (false::L) (rep d1 j ++ d0 ++ R)) =
      some (A (true::L) (rep d0 j ++ d1 ++ R)) := by
  have h := d1_scan j L (d0++R)
  have a := step_alt 0 (rep [true,true,true,true] j ++ L) R
  simp only [rep,List.nil_append,Nat.zero_add] at a
  have h' := join0 h a
  have lp : true::true::true::(rep [true,true,true,true] j ++ L) =
    rep [true,true] (2*j+1) ++ true::L := by
    rw [rep,rep11_double]
    have H := rep_snoc [true,true,true,true] j
    -- commuting the remaining singleton through an even run of ones
    have f (n : Nat) (X : List Bool) : true::(rep [true,true,true,true] n ++ X) = rep [true,true,true,true] n ++ true::X := by
      induction n with
      | zero => rfl
      | succ n ih => simp only [rep,List.cons_append,List.nil_append,List.append_assoc]; rw [← ih]
    simp only [List.cons_append,List.nil_append]; rw [f]
  rw [lp] at h'
  have h'' := join0 h' (left_pairs (2*j+1) (true::L) (true::false::R))
  rw [show 4*j+6+2*(2*j+1)=8*j+8 by omega] at h''
  rw [rep_add',pair_double] at h''
  simpa [rep,pair,d1,List.append_assoc] using h''

theorem carry (k j : Nat) (L R : List Bool) :
    run0 p (k+8*j+8) (A (false::L) (rep one k ++ rep d1 j ++ d0 ++ R)) =
      some (A (rep zero k ++ true::L) (rep d0 j ++ d1 ++ R)) := by
  cases j with
  | zero =>
    have h := step_alt k L R
    have H := join0 h (left_pair (rep zero k ++ true::L) (true::false::R))
    simpa [rep,d1,Nat.add_assoc] using H
  | succ j =>
    have h := step_double k L (rep d1 j ++ d0 ++ R) false
    have h' : run0 p (k+4) (A (false::L) (rep one k ++ rep d1 (j+1) ++ d0 ++ R)) =
      some (A (false::true::true::true::(rep zero k ++ true::L)) (rep d1 j ++ d0 ++ R)) := by
      simpa [rep,d1,List.append_assoc] using h
    have H := join0 h' (carry0 j (true::true::true::(rep zero k ++ true::L)) R)
    have H' := join0 H (left_pairs 2 (rep zero k ++ true::L) (rep d0 j ++ d1 ++ R))
    rw [show k+4+(8*j+8)+2*2=k+8*(j+1)+8 by omega] at H'
    simpa [rep,pair,d0,List.append_assoc] using H'

/-- Terminating the right scan at the implicit zero beyond 011. -/
theorem step_end (k : Nat) (L : List Bool) :
    run0 p (k+4) (A (false::L) (rep one k ++ [false,true,true])) =
      some (A (false::true::true::true::(rep zero k ++ true::L)) []) := by
  have h := start_scan k L [true,true] false
  have f (X : List Bool) : run0 p 3 (B (false::X) [true,true]) = some (A (false::true::true::true::X) []) := by rfl
  have H := join0 h (f (rep zero k ++ true::L))
  simpa only [Nat.add_assoc] using H

theorem overflow0 (j : Nat) (L : List Bool) :
    run0 p (8*j+11) (A (false::L) (rep d1 j ++ [false,true,true])) =
      some (A (true::true::L) (rep d0 (j+1) ++ [true])) := by
  induction j generalizing L with
  | zero => rfl
  | succ j ih =>
    have h : run0 p 4 (A (false::L) (rep d1 (j+1) ++ [false,true,true])) =
      some (A (false::true::true::true::true::L) (rep d1 j ++ [false,true,true])) := by rfl
    have H := join0 h (ih (true::true::true::true::L))
    have J := join0 H (left_pairs 2 (true::true::L) (rep d0 (j+1) ++ [true]))
    rw [show 4+(8*j+11)+2*2=8*(j+1)+11 by omega] at J
    simpa [rep,pair,d0] using J

theorem overflow (k j : Nat) (L : List Bool) :
    run0 p (k+8*j+11) (A (false::L) (rep one k ++ rep d1 j ++ [false,true,true])) =
      some (A (true::(rep zero k ++ true::L)) (rep d0 (j+1) ++ [true])) := by
  cases j with
  | zero =>
    have h := step_end k L
    have f (X : List Bool) : run0 p 7 (A (false::true::true::true::X) []) =
      some (A (true::X) (d0 ++ [true])) := by rfl
    have H := join0 h (f (rep zero k ++ true::L))
    simpa [rep,Nat.add_assoc] using H
  | succ j =>
    have h := step_double k L (rep d1 j ++ [false,true,true]) false
    have h' : run0 p (k+4) (A (false::L) (rep one k ++ rep d1 (j+1) ++ [false,true,true])) =
      some (A (false::true::true::true::(rep zero k ++ true::L)) (rep d1 j ++ [false,true,true])) := by
      simpa [rep,d1,List.append_assoc] using h
    have H := join0 h' (overflow0 j (true::true::true::(rep zero k ++ true::L)))
    have J := join0 H (left_pairs 2 (true::(rep zero k ++ true::L)) (rep d0 (j+1) ++ [true]))
    rw [show k+4+(8*j+11)+2*2=k+8*(j+1)+11 by omega] at J
    simpa [rep,pair,d0] using J

theorem overflow1core (j : Nat) (L : List Bool) :
    run0 p (8*j+14) (A (false::true::true::true::L) (rep d1 j ++ [true])) =
      some (A L (rep d0 (j+1) ++ [false,true,true])) := by
  induction j generalizing L with
  | zero => rfl
  | succ j ih =>
    have h : run0 p 4 (A (false::true::true::true::L) (rep d1 (j+1) ++ [true])) =
      some (A (false::true::true::true::true::true::true::true::L) (rep d1 j ++ [true])) := by rfl
    have H := join0 h (ih (true::true::true::true::L))
    have J := join0 H (left_pairs 2 L (rep d0 (j+1) ++ [false,true,true]))
    rw [show 4+(8*j+14)+2*2=8*(j+1)+14 by omega] at J
    simpa [rep,pair,d0] using J

theorem overflow1 (k j : Nat) (L : List Bool) :
    run0 p (k+8*(j+1)+10) (A (false::L) (rep one k ++ rep d1 (j+1) ++ [true])) =
      some (A (rep zero k ++ true::L) (rep d0 (j+1) ++ [false,true,true])) := by
  have h := step_double k L (rep d1 j ++ [true]) false
  have h' : run0 p (k+4) (A (false::L) (rep one k ++ rep d1 (j+1) ++ [true])) =
    some (A (false::true::true::true::(rep zero k ++ true::L)) (rep d1 j ++ [true])) := by
    simpa [rep,d1,List.append_assoc] using h
  have H := join0 h' (overflow1core j (rep zero k ++ true::L))
  rwa [show k+4+(8*j+14)=k+8*(j+1)+10 by omega] at H

/-- A virtual scanned blank and a single explicit blank agree after the first move. -/
theorem blank_left (n : Nat) (R : List Bool) :
    run0 p (n+1) (A [] R) = run0 p (n+1) (A [false] R) := by rfl

theorem seed : run0 p 29 (A [] []) = some (A [] (rep one 3 ++ d1 ++ [false,true,true])) := by rfl

#print axioms carry
#print axioms overflow
#print axioms overflow1
#print axioms blank_left
#print axioms seed
end BB6Coverage.Agent31Pump.Raw13Coupled6OneRACarry
