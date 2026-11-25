import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.LFWord68
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | _,_ => none

def O : List Bool := [true]
def Z : List Bool := [false]
def M : List Bool := [false,true,true,true,false,false,true,true]
def enc : List Bool → List Bool
  | [] => [true]
  | b::bs => b::false::false::enc bs
abbrev S := Nat × Option (List Bool)
def left : Option (List Bool) → List Bool | none => [] | some bs => enc bs
def cfg (s : S) : Z0 := ⟨1,left s.2,true::true::(rep O (3*s.1) ++ M)⟩

def next : S → S
  | (k,none) => (0,some (List.replicate k false))
  | (k,some []) => (k+1,none)
  | (k,some (true::bs)) => (k+1,some bs)
  | (k,some (false::bs)) => (0,some (List.replicate k false ++ true::bs))
def cost : S → Nat
  | (k,none) => 8+3*k
  | (_,some []) => 3
  | (_,some (true::_)) => 3
  | (k,some (false::_)) => 8+3*k

theorem zero_step (k : Nat) (l : List Bool) (hl : l.headD false = false) :
    run0 table (8+3*k) ⟨1,l,true::true::(rep O (3*k) ++ M)⟩ =
      some ⟨1,rep Z (3*k) ++ true::l.tail,true::true::M⟩ := by
  have a : run0 table 2 ⟨1,l,true::true::(rep O (3*k) ++ M)⟩ =
      some ⟨0,true::false::true::l.tail,rep O (3*k) ++ M⟩ := by
    cases l with
    | nil => rfl
    | cons b l => cases b <;> simp_all [List.headD] <;> rfl
  have b := sweepR table 0 [true] [] O Z 1 (by intro L R; rfl) (3*k) (false::true::l.tail) M
  simp only [List.nil_append,Nat.one_mul,List.cons_append] at b
  have rot (n : Nat) : rep Z n ++ false::true::l.tail = false::(rep Z n ++ true::l.tail) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change false::(rep Z n ++ false::true::l.tail) = false::false::(rep Z n ++ true::l.tail)
      rw [ih]
  rw [rot] at b
  have c : run0 table 6 ⟨0,true::false::(rep Z (3*k) ++ true::l.tail),M⟩ =
      some ⟨1,rep Z (3*k) ++ true::l.tail,true::true::M⟩ := by rfl
  have H := join0 (join0 a b) c
  rw [show 2+3*k+6=8+3*k by omega] at H
  exact H

theorem enc_zeros (k : Nat) (bs : List Bool) : enc (List.replicate k false ++ bs) = rep Z (3*k) ++ enc bs := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ,List.cons_append,enc,ih,show 3*(k+1)=3*k+3 by omega]
    rfl

theorem epoch (s : S) : run0 table (cost s) (cfg s) = some (cfg (next s)) := by
  rcases s with ⟨k,bs⟩
  cases bs with
  | none =>
    have H := zero_step k [] (by rfl)
    have e := enc_zeros k []
    simp only [List.append_nil,enc] at e
    simpa only [cfg,cost,next,left,e,List.tail_nil,rep,Nat.mul_zero,List.nil_append] using H
  | some bs =>
    cases bs with
    | nil =>
      simp only [cfg,cost,next,left,enc,show 3*(k+1)=3*k+3 by omega]
      rfl
    | cons b bs =>
      cases b with
      | true =>
        simp only [cfg,cost,next,left,enc,show 3*(k+1)=3*k+3 by omega]
        rfl
      | false =>
        have H := zero_step k (enc (false::bs)) (by rfl)
        simpa only [cfg,cost,next,left,enc_zeros,enc,List.tail_cons,rep,Nat.mul_zero,List.nil_append] using H

def orbit : Nat → S | 0 => (1,none) | n+1 => next (orbit n)
def family (n : Nat) : Z0 := cfg (orbit n)
theorem first : run0 table 32 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem positive (s : S) : 0 < cost s := by
  rcases s with ⟨k,bs⟩
  cases bs with
  | none => simp [cost]; omega
  | some bs => cases bs with
    | nil => simp [cost]
    | cons b bs => cases b <;> simp [cost] <;> omega
theorem growth (n : Nat) : run0 table (cost (orbit n)) (family n) = some (family (n+1)) := epoch (orbit n)
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 32 (fun n => cost (orbit n)) first (fun n => positive (orbit n)) growth m hm
#print axioms never
end BB6.Agent8Raw54.LFWord68
