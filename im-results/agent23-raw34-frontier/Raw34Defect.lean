import SweepPumping
namespace BB6Coverage.Agent23Defect
open BB6Coverage Agent31Pump

def e (s : Bool) : Fin 6 := if s then 5 else 4
def f (s : Bool) : Fin 6 := if s then 4 else 5

def p (s short : Bool) : PartialMachine := fun (q,b) =>
  if q = e s then
    if b then some (some ⟨false,false,f s⟩) else none
  else if q = f s then
    if b then some (some (if short then ⟨true,false,2⟩ else ⟨false,false,3⟩))
    else some (some ⟨true,false,0⟩)
  else match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,e s⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,2⟩)
  | 3,true => some (some ⟨true,true,3⟩)
  | _,_ => none

def I : List Bool := [true,false,true,false]
def O : List Bool := [true,true,true,true]
def J : List Bool := [false,true,false,true]
def P : List Bool := [true,false]
def T : List Bool := [true,true]
def k (short : Bool) : Nat := if short then 4 else 6

def hub (n b : Nat) : Z0 := ⟨0,[],rep I (n+1) ++ [false] ++ rep P b⟩

theorem first (s short : Bool) : run0 (p s short) (if short then 21 else 23) ⟨0,[],[]⟩ = some (hub 0 1) := by
  cases s <;> cases short <;> decide

theorem rightOne (s short : Bool) (L R : List Bool) :
    run0 (p s short) 4 ⟨0,[false]++L,I++R⟩ = some ⟨0,[false]++O++L,R⟩ := by
  cases s <;> cases short <;> rfl

theorem leftOne (s short : Bool) (L R : List Bool) :
    run0 (p s short) (k short) ⟨0,O++L,R⟩ = some ⟨0,L,J++R⟩ := by
  cases s <;> cases short <;> rfl

theorem rightSweep (s short : Bool) (n b : Nat) :
    run0 (p s short) (4*(n+1)) (hub n b) =
      some ⟨0,[false]++rep O (n+1),[false]++rep P b⟩ := by
  have h1 : run0 (p s short) 4 (hub n b) =
      some ⟨0,[false]++O,rep I n++[false]++rep P b⟩ := by
    cases s <;> cases short <;> rfl
  have h2 := sweepR (p s short) 0 [false] [] I O 4 (rightOne s short) n O ([false]++rep P b)
  simp only [List.nil_append] at h2
  have h2' : run0 (p s short) (4*n) ⟨0,[false]++O,rep I n++[false]++rep P b⟩ =
      some ⟨0,[false]++rep O (n+1),[false]++rep P b⟩ := by
    simpa only [List.append_assoc,← List.append_assoc (rep O n) O,rep_snoc,rep] using h2
  have h := join0 h1 h2'
  rw [show 4+4*n=4*(n+1) by omega] at h
  exact h

theorem commute (n : Nat) : T++rep O n = rep O n++T := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change T++(O++rep O n) = (O++rep O n)++T
    rw [← List.append_assoc, show T++O=O++T by rfl, List.append_assoc,ih,List.append_assoc]

theorem rotateEnd (n : Nat) (R : List Bool) :
    [true,false,true]++(rep J n++([false,false]++R)) = rep I (n+1)++([false]++R) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change [true,false,true]++((J++rep J n)++([false,false]++R)) = (I++rep I (n+1))++([false]++R)
    simp only [List.append_assoc]
    rw [← List.append_assoc [true,false,true] J, show [true,false,true]++J=I++[true,false,true] by rfl, List.append_assoc, ih]

theorem moveDefect (s short : Bool) (n b : Nat) :
    run0 (p s short) ((4+k short)*(n+1)+6) (hub n (b+1)) = some (hub (n+1) b) := by
  have h1 := rightSweep s short n (b+1)
  have h2 : run0 (p s short) 3 ⟨0,[false]++rep O (n+1),[false]++rep P (b+1)⟩ =
      some ⟨0,T++rep O (n+1),[false,false]++rep P b⟩ := by
    cases s <;> cases short <;> rfl
  rw [commute] at h2
  have h3 : run0 (p s short) (k short*(n+1)) ⟨0,rep O (n+1)++T,[false,false]++rep P b⟩ =
      some ⟨0,T,rep J (n+1)++([false,false]++rep P b)⟩ := by
    simpa using sweepL (p s short) 0 [] [] O J (k short) (by intro L R; exact leftOne s short L R) (n+1) T ([false,false]++rep P b)
  have h4 : run0 (p s short) 3 ⟨0,T,rep J (n+1)++([false,false]++rep P b)⟩ =
      some ⟨0,[],[true,false,true]++(rep J (n+1)++([false,false]++rep P b))⟩ := by
    cases s <;> cases short <;> rfl
  rw [rotateEnd] at h4
  have H := join0 (join0 (join0 h1 h2) h3) h4
  have he : 4*(n+1)+3+k short*(n+1)+3 = (4+k short)*(n+1)+6 := by cases short <;> simp [k] <;> omega
  rw [he] at H
  simpa only [hub,List.append_assoc] using H

theorem resetWord (n : Nat) : rep J (n+2)++[false] = [false,true]++[false]++rep P (2*n+3) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (J++rep J (n+2))++[false] = [false,true]++[false]++rep P (2*(n+1)+3)
    rw [List.append_assoc,ih]
    rw [show 2*(n+1)+3=(2*n+3)+2 by omega]
    rfl

theorem reset (s short : Bool) (n : Nat) :
    run0 (p s short) ((4+k short)*(n+1)+k short+17) (hub n 0) = some (hub 0 (2*n+3)) := by
  have h1 := rightSweep s short n 0
  have h2 : run0 (p s short) 11 ⟨0,[false]++rep O (n+1),[false]++rep P 0⟩ =
      some ⟨0,rep O (n+2),[false]⟩ := by
    cases s <;> cases short <;> rfl
  have h3 : run0 (p s short) (k short*(n+2)) ⟨0,rep O (n+2),[false]⟩ =
      some ⟨0,[],rep J (n+2)++[false]⟩ := by
    simpa using sweepL (p s short) 0 [] [] O J (k short) (by intro L R; exact leftOne s short L R) (n+2) [] [false]
  rw [resetWord] at h3
  have h4 : run0 (p s short) 6 ⟨0,[],[false,true]++[false]++rep P (2*n+3)⟩ =
      some (hub 0 (2*n+3)) := by
    cases s <;> cases short <;> rfl
  have H := join0 (join0 (join0 h1 h2) h3) h4
  have he : 4*(n+1)+11+k short*(n+2)+6 = (4+k short)*(n+1)+k short+17 := by cases short <;> simp [k] <;> omega
  rw [he] at H
  exact H

def params : Nat → Nat × Nat
  | 0 => (0,1)
  | t+1 => match params t with
    | (i,0) => (0,2*i+3)
    | (i,j+1) => (i+1,j)
def family (t : Nat) : Z0 := hub (params t).1 (params t).2
def cost (short : Bool) (t : Nat) : Nat := match params t with
  | (n,0) => (4+k short)*(n+1)+k short+17
  | (n,_+1) => (4+k short)*(n+1)+6

theorem growth (s short : Bool) (t : Nat) : run0 (p s short) (cost short t) (family t) = some (family (t+1)) := by
  cases h : params t with
  | mk i j =>
    cases j with
    | zero => simpa [family,cost,params,h] using reset s short i
    | succ j => simpa [family,cost,params,h] using moveDefect s short i j

theorem positive (short : Bool) (t : Nat) : 0 < cost short t := by
  cases h : params t with
  | mk i j => cases j <;> simp [cost,h] <;> omega

theorem never (s short : Bool) (m : Machine) (hm : compatible (p s short) m) : NeverHalts m :=
  never_of_growth (p s short) family (if short then 21 else 23) (cost short)
    (first s short) (positive short) (growth s short) m hm

#print axioms moveDefect
#print axioms reset
#print axioms never
end BB6Coverage.Agent23Defect
