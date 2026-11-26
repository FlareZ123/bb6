import SweepPumping
import FastFAR

namespace BB6Coverage.Agent48.E0OneLA
open BB6Coverage BB6Coverage.Agent31Pump

set_option maxRecDepth 4096
set_option maxHeartbeats 0

abbrev O (n : Nat) := rep [true] n
abbrev P (n : Nat) := rep [false,true] n
abbrev Q (n : Nat) := rep [true,true] n
abbrev W (n : Nat) := rep [true,false] n

def p (x : Bool) : PartialMachine := FAR.fromCodes [7,18,11,9,14,21,(if x then 23 else 19),16,2,11,24,11]

theorem catO (a b : Nat) : O a ++ O b = O (a+b) := by
  induction a with
  | zero => simp [rep]
  | succ a ih => simp only [Nat.succ_add,rep,List.cons_append,List.nil_append,ih]

theorem qO (n : Nat) : Q n = O (2*n) := by
  induction n with
  | zero => simp [rep]
  | succ n ih => simp only [rep,ih,Nat.mul_succ]; rfl

theorem rotateP (n : Nat) : false :: (W n ++ [true]) = P (n+1) := by
  induction n with
  | zero => simp [rep]
  | succ n ih => simp only [rep,List.cons_append,List.nil_append]; change false :: true :: (false :: (W n ++ [true])) = _; rw [ih]; rfl

-- E/F on a 1 begin a rightward alternating-writing sweep. B1 writes 0 instead.
theorem returnEF (x : Bool) (f : Bool) (n : Nat) (L R : List Bool) :
    run0 (p x) (2*n+1) ⟨if f then 5 else 4,true::L,Q n ++ false::R⟩ =
      some ⟨2,false :: (W n ++ true::L),R⟩ := by
  induction n generalizing f L with
  | zero => cases x <;> cases f <;> rfl
  | succ n ih =>
    have h : run0 (p x) 2 ⟨if f then 5 else 4,true::L,Q (n+1) ++ false::R⟩ =
        some ⟨5,true::false::true::L,Q n ++ false::R⟩ := by cases x <;> cases f <;> rfl
    have g := ih true (false::true::L)
    have H := join0 h g
    rw [show 2+(2*n+1)=2*(n+1)+1 by omega] at H
    have eq : W n ++ true::false::true::L = W (n+1) ++ true::L := by
      calc
        _ = (W n ++ [true,false]) ++ true::L := by simp only [List.append_assoc,List.cons_append,List.nil_append]
        _ = _ := by rw [rep_snoc]; rfl
    rw [eq] at H
    exact H

theorem returnB (x : Bool) (n : Nat) (L R : List Bool) :
    run0 (p x) (2*n+1) ⟨1,true::L,Q n ++ false::R⟩ =
      some ⟨2,false :: (W n ++ false::L),R⟩ := by
  cases n with
  | zero => cases x <;> rfl
  | succ n =>
    have h : run0 (p x) 2 ⟨1,true::L,Q (n+1) ++ false::R⟩ = some ⟨5,true::false::false::L,Q n ++ false::R⟩ := by cases x <;> rfl
    have H := join0 h (returnEF x true n (false::false::L) R)
    rw [show 2+(2*n+1)=2*(n+1)+1 by omega] at H
    have eq : W n ++ true::false::false::L = W (n+1) ++ false::L := by
      calc
        _ = (W n ++ [true,false]) ++ false::L := by simp only [List.append_assoc,List.cons_append,List.nil_append]
        _ = _ := by rw [rep_snoc]; rfl
    rw [eq] at H
    exact H

theorem returnEnd (x f : Bool) (n : Nat) (L : List Bool) :
    run0 (p x) (2*n+1) ⟨if f then 5 else 4,true::L,Q n⟩ =
      some ⟨2,false :: (W n ++ true::L),[]⟩ := by
  induction n generalizing f L with
  | zero => cases x <;> cases f <;> rfl
  | succ n ih =>
    have h : run0 (p x) 2 ⟨if f then 5 else 4,true::L,Q (n+1)⟩ = some ⟨5,true::false::true::L,Q n⟩ := by cases x <;> cases f <;> rfl
    have H := join0 h (ih true (false::true::L))
    rw [show 2+(2*n+1)=2*(n+1)+1 by omega] at H
    have eq : W n ++ true::false::true::L = W (n+1) ++ true::L := by
      calc
        _ = (W n ++ [true,false]) ++ true::L := by simp only [List.append_assoc,List.cons_append,List.nil_append]
        _ = _ := by rw [rep_snoc]; rfl
    rw [eq] at H
    exact H

-- C0,D1 followed by n copies of E0,A1 moves left through alternating bits.
theorem leftPass (x : Bool) (n : Nat) (L R : List Bool) :
    run0 (p x) (2+2*n) ⟨2,P (n+1) ++ L,R⟩ = some ⟨4,L,Q n ++ false::true::R⟩ := by
  have h : run0 (p x) 2 ⟨2,P (n+1) ++ L,R⟩ = some ⟨4,P n ++ L,false::true::R⟩ := by cases x <;> rfl
  have s := sweepL (p x) 4 [] [] [false,true] [true,true] 2 (by intro A B; cases x <;> rfl) n L (false::true::R)
  exact join0 h s

theorem drainOne (x : Bool) (n m k : Nat) :
    run0 (p x) (4*n+3) ⟨2,P (n+1) ++ O (m+1), O k⟩ = some ⟨2,P (n+1) ++ O m,O (k+1)⟩ := by
  have H := join0 (leftPass x n (O (m+1)) (O k)) (returnEF x false n (O m) (true::O k))
  rw [show 2+2*n+(2*n+1)=4*n+3 by omega] at H
  have eq : false :: (W n ++ true::O m) = P (n+1) ++ O m := by
    have h := rotateP n
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using congrArg (fun a => a ++ O m) h
  rw [eq] at H
  exact H

theorem drainAll (x : Bool) (n m k : Nat) :
    run0 (p x) ((4*n+3)*m) ⟨2,P (n+1) ++ O m,O k⟩ = some ⟨2,P (n+1),O (k+m)⟩ := by
  induction m generalizing k with
  | zero => simp [rep,run0]
  | succ m ih =>
    have H := join0 (drainOne x n m k) (ih (k+1))
    rw [show (4*n+3)+(4*n+3)*m=(4*n+3)*(m+1) by rw [Nat.mul_succ,Nat.add_comm]] at H
    simpa only [Nat.add_assoc,Nat.add_comm 1 m] using H

theorem seedTurn (x : Bool) (n k : Nat) :
    run0 (p x) (4*n+5) ⟨2,P (n+1),O k⟩ = some ⟨2,P n ++ [false,false,true],O (k+1)⟩ := by
  have h := leftPass x n [] (O k)
  have h' : run0 (p x) (2+2*n) ⟨2,P (n+1),O k⟩ = some ⟨4,[],Q n ++ false::true::O k⟩ := by simpa only [List.append_nil] using h
  have g : run0 (p x) 2 ⟨4,[],Q n ++ false::true::O k⟩ = some ⟨1,[true,true],Q n ++ false::true::O k⟩ := by cases x <;> rfl
  have H := join0 (join0 h' g) (returnB x n [true] (true::O k))
  rw [show 2+2*n+2+(2*n+1)=4*n+5 by omega] at H
  have eq : false :: (W n ++ [false,true]) = P n ++ [false,false,true] := by
    have rot := rotate false [true] n
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using congrArg (fun a => a ++ [false,true]) rot
  rw [eq] at H
  exact H

theorem drainAlt (x : Bool) (n m k : Nat) :
    run0 (p x) (4*n+5) ⟨2,P (n+1) ++ false::false::O m,O k⟩ = some ⟨2,P n ++ false::false::O (m+1),O (k+1)⟩ := by
  have h := leftPass x n (false::false::O m) (O k)
  have g : run0 (p x) 2 ⟨4,false::false::O m,Q n ++ false::true::O k⟩ = some ⟨1,true::true::O m,Q n ++ false::true::O k⟩ := by cases x <;> rfl
  have H := join0 (join0 h g) (returnB x n (true::O m) (true::O k))
  rw [show 2+2*n+2+(2*n+1)=4*n+5 by omega] at H
  have eq : false :: (W n ++ false::true::O m) = P n ++ false::false::O (m+1) := by
    have rot := rotate false [true] n
    simpa only [rep,List.append_assoc,List.cons_append,List.nil_append] using congrArg (fun a => a ++ false::true::O m) rot
  rw [eq] at H
  exact H

def altCost : Nat → Nat
  | 0 => 0
  | n+1 => 4*n+5+altCost n

theorem drainAltAll (x : Bool) (n m k : Nat) :
    run0 (p x) (altCost n) ⟨2,P n ++ false::false::O m,O k⟩ = some ⟨2,false::false::O (m+n),O (k+n)⟩ := by
  induction n generalizing m k with
  | zero => rfl
  | succ n ih =>
    have H := join0 (drainAlt x n m k) (ih (m+1) (k+1))
    simpa only [altCost,Nat.add_assoc,Nat.add_comm 1 n] using H

theorem finishTurn (x : Bool) (n : Nat) :
    run0 (p x) (2*n+3) ⟨2,false::false::O n,O (2*n)⟩ = some ⟨2,P (n+1) ++ O (n+1),[]⟩ := by
  have h : run0 (p x) 2 ⟨2,false::false::O n,O (2*n)⟩ = some ⟨if x then 5 else 4,true::true::O n,O (2*n)⟩ := by cases x <;> rfl
  rw [← qO] at h
  have H := join0 h (returnEnd x x n (true::O n))
  rw [show 2+(2*n+1)=2*n+3 by omega] at H
  have eq : false :: (W n ++ true::true::O n) = P (n+1) ++ O (n+1) := by
    have rot := rotateP n
    simpa only [rep,List.append_assoc,List.cons_append,List.nil_append] using congrArg (fun a => a ++ true::O n) rot
  rw [eq] at H
  rw [← qO]
  exact H

def family (n : Nat) : Z0 := ⟨2,P (n+1) ++ O (n+1),[]⟩
def cost (n : Nat) : Nat := (4*n+3)*(n+1)+(4*n+5)+altCost n+(2*(n+1)+3)

theorem growth (x : Bool) (n : Nat) : run0 (p x) (cost n) (family n) = some (family (n+1)) := by
  have h := drainAll x n (n+1) 0
  have h1 : run0 (p x) ((4*n+3)*(n+1)) (family n) = some ⟨2,P (n+1),O (n+1)⟩ := by simpa only [family,Nat.zero_add,rep] using h
  have h2 := seedTurn x n (n+1)
  have h3 := drainAltAll x n 1 (n+2)
  have e1 : P n ++ [false,false,true] = P n ++ false::false::O 1 := rfl
  rw [e1] at h2
  have H := join0 (join0 h1 h2) h3
  rw [show 1+n=n+1 by omega,show n+2+n=2*(n+1) by omega] at H
  have H' := join0 H (finishTurn x (n+1))
  exact H'

theorem nonhalt (x : Bool) (m : Machine) (hm : compatible (p x) m) : NeverHalts m := by
  apply never_of_growth (p x) family 2 cost
  · cases x <;> rfl
  · intro n; unfold cost; omega
  · exact growth x
  · exact hm

#print axioms nonhalt
end BB6Coverage.Agent48.E0OneLA
