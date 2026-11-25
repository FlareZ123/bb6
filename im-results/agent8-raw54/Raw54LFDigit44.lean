import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.LFDigit44
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨false,true,0⟩)
  | _,_ => none

def O : List Bool := [true]
def Z : List Bool := [false]
def sixO : List Bool := [true,true,true,true,true,true]
def sixZ : List Bool := [false,false,false,false,false,false]
def A (n : Nat) (R : List Bool) : Z0 := ⟨0,false::(rep O n ++ [false,false]),false::R⟩

theorem carry (n : Nat) (T : List Bool) :
    run0 table 10 (A n (sixO ++ T)) = some (A (n+6) T) := by rfl

theorem zeros (n : Nat) (T : List Bool) :
    run0 table (n+10) (A n (false::false::T)) = some (A 0 (rep Z n ++ true::true::T)) := by
  have a : run0 table 6 (A n (false::false::T)) =
      some ⟨4,rep O (n+1) ++ [false,false],false::true::true::T⟩ := by rfl
  have b := sweepL table 4 [] [] O Z 1 (by intro L R; rfl) (n+1) [false,false] (false::true::true::T)
  simp only [List.nil_append,Nat.one_mul] at b
  have hZ : rep Z (n+1) ++ false::true::true::T = false::false::(rep Z n ++ true::true::T) := by
    clear a b
    induction n with
    | zero => rfl
    | succ n ih => simp only [rep,Z,List.cons_append,List.nil_append] at ih ⊢; rw [ih]
  rw [hZ] at b
  have c : run0 table 3 ⟨4,[false,false],false::false::(rep Z n ++ true::true::T)⟩ =
      some (A 0 (rep Z n ++ true::true::T)) := by rfl
  have H := join0 (join0 a b) c
  rw [show 6+(n+1)+3=n+10 by omega] at H
  exact H

theorem blankReset (n : Nat) :
    run0 table (n+10) (A n []) = some (A 0 (rep Z n ++ [true,true])) := by
  have a : run0 table 6 (A n []) =
      some ⟨4,rep O (n+1) ++ [false,false],[false,true,true]⟩ := by rfl
  have a' : run0 table 6 (A n [false,false]) =
      some ⟨4,rep O (n+1) ++ [false,false],[false,true,true]⟩ := by rfl
  have H := zeros n []
  rw [show n+10=6+(n+4) by omega,run0_add,a'] at H
  rw [show n+10=6+(n+4) by omega,run0_add,a]
  exact H

theorem oneReset (n : Nat) (T : List Bool) :
    run0 table (n+26) (A n (true::true::false::false::false::false::T)) =
      some (A 0 (rep Z (n+2) ++ true::true::true::true::T)) := by
  have a : run0 table 14 (A n (true::true::false::false::false::false::T)) =
      some (A (n+2) (false::false::true::true::T)) := by rfl
  have b := zeros (n+2) (true::true::T)
  have H := join0 a b
  rw [show 14+(n+2+10)=n+26 by omega] at H
  exact H

theorem oneBlank (n : Nat) :
    run0 table (n+26) (A n [true,true]) = some (A 0 (rep Z (n+2) ++ [true,true,true,true])) := by
  have a : run0 table 14 (A n [true,true]) =
      some (A (n+2) [false,false,true,true]) := by rfl
  have H := join0 a (zeros (n+2) [true,true])
  rw [show 14+(n+2+10)=n+26 by omega] at H
  exact H

inductive Digit where | d0 | d1 | d2 | d3
inductive Word where | one | two | three | cons : Digit → Word → Word

def block : Digit → List Bool
  | .d0 => sixZ
  | .d1 => [true,true,false,false,false,false]
  | .d2 => [false,false,true,true,true,true]
  | .d3 => sixO

def enc : Word → List Bool
  | .one => [true,true]
  | .two => block .d2
  | .three => sixO
  | .cons d w => block d ++ enc w

def bump : Word → Word
  | .one => .two
  | .two => .three
  | .three => .cons .d0 .one
  | .cons .d0 w => .cons .d1 w
  | .cons .d1 w => .cons .d2 w
  | .cons .d2 w => .cons .d3 w
  | .cons .d3 w => .cons .d0 (bump w)
def cost : Word → Nat
  | .one => 26
  | .two => 10
  | .three => 26
  | .cons .d0 _ => 10
  | .cons .d1 _ => 26
  | .cons .d2 _ => 10
  | .cons .d3 w => 16+cost w

theorem zshift (n : Nat) (T : List Bool) :
    rep Z (n+6) ++ T = rep Z n ++ sixZ ++ T := by
  induction n with
  | zero => rfl
  | succ n ih => rw [show n+1+6=n+6+1 by omega]; change false::(rep Z (n+6) ++ T) = false::(rep Z n ++ sixZ ++ T); rw [ih]

theorem zshift2 (n : Nat) (T : List Bool) :
    rep Z (n+2) ++ T = rep Z n ++ false::false::T := by
  induction n with
  | zero => rfl
  | succ n ih => rw [show n+1+2=n+2+1 by omega]; change false::(rep Z (n+2) ++ T) = false::(rep Z n ++ false::false::T); rw [ih]

theorem epoch (w : Word) (n : Nat) :
    run0 table (n+cost w) (A n (enc w)) = some (A 0 (rep Z n ++ enc (bump w))) := by
  induction w generalizing n with
  | one =>
    have H := oneBlank n
    rw [zshift2] at H
    exact H
  | two => exact zeros n [true,true,true,true]
  | three =>
    have a := carry n []
    have H := join0 a (blankReset (n+6))
    rw [show 10+(n+6+10)=n+26 by omega,zshift,List.append_nil] at H
    simpa only [cost,enc,bump,block,List.append_assoc] using H
  | cons d w ih =>
    cases d with
    | d0 => exact zeros n (false::false::false::false::enc w)
    | d1 =>
      have H := oneReset n (enc w)
      rw [zshift2] at H
      exact H
    | d2 => exact zeros n (true::true::true::true::enc w)
    | d3 =>
      have H := join0 (carry n (enc w)) (ih (n+6))
      rw [show 10+(n+6+cost w)=n+(16+cost w) by omega,zshift] at H
      simpa only [cost,enc,bump,block,List.append_assoc] using H

def orbit : Nat → Word | 0 => .one | n+1 => bump (orbit n)
def family (n : Nat) : Z0 := A 0 (enc (orbit n))
theorem first : run0 table 10 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem positive (w : Word) : 0 < cost w := by cases w with
  | one | two | three => decide
  | cons d w => cases d <;> simp [cost] <;> omega
theorem growth (n : Nat) : run0 table (cost (orbit n)) (family n) = some (family (n+1)) := by
  simpa only [family,orbit,Nat.zero_add,rep,List.nil_append] using epoch (orbit n) 0
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 10 (fun n => cost (orbit n)) first (fun n => positive (orbit n)) growth m hm
#print axioms never
end BB6.Agent8Raw54.LFDigit44
