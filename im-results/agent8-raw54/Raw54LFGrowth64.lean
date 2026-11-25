import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.LFGrowth64
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,true,2⟩)
  | _,_ => none

def Z : List Bool := [false,false]
def O : List Bool := [true,true]
def P0 : List Bool := [true,true]
def P1 : List Bool := [true,false,true,true]
def P2 : List Bool := [true,false,true,false,true,true]
def cfg (p : List Bool) (n : Nat) : Z0 := ⟨3,rep Z n ++ p,[]⟩

theorem zero_rotate (n : Nat) (p : List Bool) :
    rep Z n ++ false::p = false::(rep Z n ++ p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change false::false::(rep Z n ++ false::p) = false::false::false::(rep Z n ++ p)
    rw [ih]

theorem drain (n : Nat) (p : List Bool) :
    run0 table (2*n+2) ⟨5,true::false::p,rep O n⟩ = some (cfg p (n+2)) := by
  have a := sweepR table 5 [true] [] O Z 2 (by intro L R; rfl) n (false::p) []
  simp only [List.nil_append,List.append_nil,List.cons_append] at a
  have b : run0 table 2 ⟨5,true::(rep Z n ++ false::p),[]⟩ =
      some ⟨3,false::false::false::(rep Z n ++ false::p),[]⟩ := by rfl
  have H := join0 a b
  rw [zero_rotate] at H
  simpa only [cfg,rep,Z,List.cons_append,List.nil_append] using H

theorem pump (n : Nat) (p : List Bool) :
    run0 table (2*n) (cfg p n) = some ⟨3,p,rep O n⟩ := by
  simpa only [cfg,List.nil_append,List.append_nil] using
    sweepL table 3 [] [] Z O 2 (by intro L R; rfl) n p []

theorem big (k : Nat) :
    run0 table (4*k+56) (cfg P0 (k+2)) = some (cfg P2 (k+3)) := by
  have a := pump (k+2) P0
  have b : run0 table 48 ⟨3,P0,rep O (k+2)⟩ = some ⟨5,true::false::P2,rep O (k+1)⟩ := by
    simp only [rep,O,List.cons_append,List.nil_append]
    rfl
  have H := join0 (join0 a b) (drain (k+1) P2)
  rw [show 2*(k+2)+48+(2*(k+1)+2)=4*k+56 by omega] at H
  exact H

theorem small2 (n : Nat) :
    run0 table (4*n+12) (cfg P2 n) = some (cfg P1 (n+2)) := by
  have a := pump n P2
  have b : run0 table 10 ⟨3,P2,rep O n⟩ = some ⟨5,true::false::P1,rep O n⟩ := by rfl
  have H := join0 (join0 a b) (drain n P1)
  rw [show 2*n+10+(2*n+2)=4*n+12 by omega] at H
  exact H

theorem small1 (n : Nat) :
    run0 table (4*n+12) (cfg P1 n) = some (cfg P0 (n+2)) := by
  have a := pump n P1
  have b : run0 table 10 ⟨3,P1,rep O n⟩ = some ⟨5,true::false::P0,rep O n⟩ := by rfl
  have H := join0 (join0 a b) (drain n P0)
  rw [show 2*n+10+(2*n+2)=4*n+12 by omega] at H
  exact H

def family (n : Nat) : Z0 := cfg P0 (5*n+6)
theorem first : run0 table 103 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (60*n+160) (family n) = some (family (n+1)) := by
  have a := big (5*n+4)
  have b := small2 (5*n+4+3)
  have c := small1 (5*n+4+3+2)
  have H := join0 (join0 a b) c
  rw [show 4*(5*n+4)+56+(4*(5*n+4+3)+12)+(4*(5*n+4+3+2)+12)=60*n+160 by omega] at H
  unfold family
  rw [show 5*n+4+2=5*n+6 by omega, show 5*n+4+3+2+2=5*(n+1)+6 by omega] at H
  exact H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 103 (fun n => 60*n+160) first (by intro n; omega) growth m hm
#print axioms never
end BB6.Agent8Raw54.LFGrowth64
