import SweepPumping
namespace BB6Coverage.Agent23Odometer
open BB6Coverage Agent31Pump

def e (s : Bool) : Fin 6 := if s then 5 else 4
def f (s : Bool) : Fin 6 := if s then 4 else 5

def p (s wide : Bool) : PartialMachine := fun (q,b) =>
  if q = e s then
    if b then some (some (if wide then ⟨false,false,2⟩ else ⟨false,false,f s⟩))
    else some (some (if wide then ⟨true,false,f s⟩ else ⟨true,false,0⟩))
  else if q = f s then
    if b then if wide then none else some (some ⟨true,false,1⟩)
    else if wide then some (some ⟨true,false,0⟩) else none
  else match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,e s⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,2⟩)
  | 3,true => some (some ⟨true,true,3⟩)
  | _,_ => none

def w (wide : Bool) : Nat := if wide then 3 else 2
def digit (wide b : Bool) : List Bool := b :: rep [false] (w wide-1)
def enc (wide : Bool) : List Bool → List Bool
  | [] => []
  | b::bs => digit wide b ++ enc wide bs

def bump : List Bool → List Bool
  | [] => [false]
  | false::bs => true::bs
  | true::bs => false::bump bs

def pre : List Bool := [false,true,false,true]
def tail : List Bool := [false,false,true,false]
def hub (wide : Bool) (bits : List Bool) : Z0 :=
  ⟨3,pre ++ rep [false] (if wide then 0 else 2) ++ enc wide bits ++ [true],[]⟩

theorem repAdd (P : List Bool) (n m : Nat) : rep P (n+m) = rep P n ++ rep P m := by
  induction n with
  | zero => simp [rep]
  | succ n ih => rw [show n+1+m=(n+m)+1 by omega,rep,ih,rep,List.append_assoc]

theorem backOne (s wide : Bool) (L R : List Bool) :
  run0 (p s wide) 1 ⟨1,[true]++L,[true]++R⟩ = some ⟨1,[true]++[false]++L,R⟩ := by
  cases s <;> cases wide <;> rfl

theorem back (s wide : Bool) (t : Nat) (L : List Bool) :
    run0 (p s wide) (t+4) ⟨0,false::L,rep [true] t ++ tail⟩ =
    some ⟨3,pre ++ rep [false] t ++ [true] ++ L,[]⟩ := by
  cases t with
  | zero => cases s <;> cases wide <;> rfl
  | succ n =>
    have h1 : run0 (p s wide) 1 ⟨0,false::L,rep [true] (n+1) ++ tail⟩ = some ⟨1,[true,true]++L,rep [true] n++tail⟩ := by
      cases s <;> cases wide <;> rfl
    have h2 : run0 (p s wide) n ⟨1,[true,true]++L,rep [true] n++tail⟩ = some ⟨1,[true]++rep [false] n++[true]++L,tail⟩ := by
      simpa only [Nat.one_mul,List.nil_append,List.append_assoc,List.cons_append] using sweepR (p s wide) 1 [true] [] [true] [false] 1 (backOne s wide) n ([true]++L) tail
    have h3 : run0 (p s wide) 4 ⟨1,[true]++rep [false] n++[true]++L,tail⟩ = some ⟨3,pre++rep [false] (n+1)++[true]++L,[]⟩ := by
      cases s <;> cases wide <;> rfl
    have H := join0 (join0 h1 h2) h3
    rw [show 1+n+4=n+1+4 by omega] at H
    exact H

theorem backEmpty (s wide : Bool) (t : Nat) :
    run0 (p s wide) (t+4) ⟨0,[],rep [true] t ++ tail⟩ =
    some ⟨3,pre ++ rep [false] t ++ [true],[]⟩ := by
  have H := back s wide t []
  simp only [List.append_nil] at H
  exact H

theorem carryOne (s wide : Bool) (L R : List Bool) :
    run0 (p s wide) (w wide) ⟨0,digit wide true ++ L,R⟩ =
      some ⟨0,L,rep [true] (w wide) ++ R⟩ := by
  cases s <;> cases wide <;> rfl

theorem carryEnd (s wide : Bool) (R : List Bool) :
    run0 (p s wide) (w wide) ⟨0,[true],R⟩ =
      some ⟨0,[],rep [true] (w wide) ++ R⟩ := by
  cases s <;> cases wide <;> rfl

def cc (wide : Bool) : List Bool → Nat → Nat
  | [],t => w wide+(t+w wide+4)
  | false::_,t => t+4
  | true::bs,t => w wide+cc wide bs (t+w wide)

theorem digitZero (wide : Bool) : digit wide false = rep [false] (w wide) := by cases wide <;> rfl

theorem carry (s wide : Bool) (bits : List Bool) (t : Nat) :
    run0 (p s wide) (cc wide bits t) ⟨0,enc wide bits++[true],rep [true] t++tail⟩ =
      some ⟨3,pre++rep [false] t++enc wide (bump bits)++[true],[]⟩ := by
  induction bits generalizing t with
  | nil =>
    have h1 := carryEnd s wide (rep [true] t++tail)
    have h2 := backEmpty s wide (t+w wide)
    rw [Nat.add_comm t (w wide),repAdd [true],List.append_assoc] at h2
    have H := join0 h1 h2
    rw [Nat.add_comm (w wide) t] at H
    simpa only [cc,enc,List.nil_append,bump,digitZero,repAdd,List.append_assoc] using H
  | cons b bs ih =>
    cases b with
    | false =>
      simpa only [cc,enc,digit,bump,List.cons_append,List.nil_append,List.append_assoc] using back s wide t (rep [false] (w wide-1)++enc wide bs++[true])
    | true =>
      have h1 := carryOne s wide (enc wide bs++[true]) (rep [true] t++tail)
      have h2 := ih (t+w wide)
      rw [Nat.add_comm t (w wide),repAdd [true],List.append_assoc] at h2
      have H := join0 h1 h2
      rw [Nat.add_comm (w wide) t] at H
      simpa only [cc,enc,bump,digitZero,repAdd,List.append_assoc] using H

theorem prefixRun (s wide : Bool) (bits : List Bool) :
    run0 (p s wide) (if wide then 8 else 12) (hub wide bits) =
      some ⟨0,enc wide bits++[true],rep [true] (if wide then 0 else 2)++tail⟩ := by
  cases s <;> cases wide <;> rfl

def initial (_wide : Bool) : List Bool := []
theorem first (s wide : Bool) : run0 (p s wide) (if wide then 6 else 28) ⟨0,[],[]⟩ = some (hub wide (initial wide)) := by
  cases s <;> cases wide <;> decide

def bitsAt (wide : Bool) : Nat → List Bool
  | 0 => initial wide
  | n+1 => bump (bitsAt wide n)
def family (wide : Bool) (n : Nat) : Z0 := hub wide (bitsAt wide n)
def cost (wide : Bool) (n : Nat) := (if wide then 8 else 12) + cc wide (bitsAt wide n) (if wide then 0 else 2)
theorem positive (wide : Bool) (n : Nat) : 0 < cost wide n := by
  cases wide <;> simp [cost] <;> omega

theorem growth (s wide : Bool) (n : Nat) : run0 (p s wide) (cost wide n) (family wide n) = some (family wide (n+1)) := by
  exact join0 (prefixRun s wide (bitsAt wide n)) (carry s wide (bitsAt wide n) (if wide then 0 else 2))

theorem never (s wide : Bool) (m : Machine) (hm : compatible (p s wide) m) : NeverHalts m :=
  never_of_growth (p s wide) (family wide) (if wide then 6 else 28) (cost wide)
    (first s wide) (positive wide) (growth s wide) m hm

#print axioms carry
#print axioms growth
#print axioms never
end BB6Coverage.Agent23Odometer
