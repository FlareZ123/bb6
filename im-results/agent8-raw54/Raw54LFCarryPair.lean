import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.LFCarryPair
open BB6Coverage BB6Coverage.Agent31Pump

-- false = LF84, true = LF105
def table (v : Bool) : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => if v then none else some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => if v then some (some ⟨true,true,0⟩) else none
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,if v then 1 else 0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,true,if v then 2 else 0⟩)
  | 5,true => some (some ⟨false,true,if v then 2 else 0⟩)
  | _,_ => none

def O : List Bool := [true]
def Z : List Bool := [false]
def width (v : Bool) : Nat := if v then 4 else 3
def frame (v : Bool) : List Bool := if v then [true,false,false,false,false,true,true] else [true,false,false,false,false,false,true,true]
def digit (v b : Bool) : List Bool := if v then [false,false,b,b] else [false,b,b]
def enc (v : Bool) : List Bool → List Bool
  | [] => []
  | b::bs => digit v b ++ enc v bs
def bump : List Bool → List Bool
  | [] => [true]
  | false::bs => true::bs
  | true::bs => false::bump bs
def carries : List Bool → Nat
  | [] => 0
  | false::_ => 0
  | true::bs => carries bs+1

def cfg (v : Bool) (bs : List Bool) : Z0 := ⟨5,[true,true],frame v ++ enc v bs⟩
def scanCfg (v : Bool) (k : Nat) (R : List Bool) : Z0 := ⟨if v then 1 else 0,true::(rep O (width v*k+(if v then 5 else 6)) ++ [false,true,false]),R⟩

theorem rep_add (P : List Bool) (n m : Nat) : rep P (n+m) = rep P n ++ rep P m := by
  induction n with
  | zero => simp [rep]
  | succ n ih => rw [show n+1+m=n+m+1 by omega]; simp only [rep,ih,List.append_assoc]

theorem enter (v : Bool) (bs : List Bool) : run0 (table v) (if v then 21 else 22) (cfg v bs) = some (scanCfg v 0 (enc v bs)) := by
  cases v <;> rfl

theorem scan_one (v : Bool) (k : Nat) (T : List Bool) :
    run0 (table v) (width v) (scanCfg v k (digit v true ++ T)) = some (scanCfg v (k+1) T) := by
  cases v
  · unfold scanCfg
    simp only [width,Bool.false_eq_true,ite_false, Bool.not_false,show 3*(k+1)+6=3+(3*k+6) by omega,rep_add O 3]
    rfl
  · unfold scanCfg
    simp only [width,ite_true,Bool.not_true,show 4*(k+1)+5=4+(4*k+5) by omega,rep_add O 4]
    rfl

theorem scan_zero (v : Bool) (k : Nat) (T : List Bool) :
    run0 (table v) (if v then 7 else 6) (scanCfg v k (digit v false ++ T)) =
    some ⟨4,rep O (width v*k+7) ++ [false,true,false],false::true::true::T⟩ := by
  cases v <;> simp only [scanCfg,width,ite_true,ite_false,Bool.false_eq_true,Bool.not_false,Bool.not_true,show ∀ n : Nat, n+7=1+(n+6) by omega,rep_add O 1,show ∀ n : Nat, n+6=1+(n+5) by omega] <;> rfl

theorem scan_blank (v : Bool) (k : Nat) :
    run0 (table v) (if v then 7 else 6) (scanCfg v k []) =
    some ⟨4,rep O (width v*k+7) ++ [false,true,false],[false,true,true]⟩ := by
  cases v <;> simp only [scanCfg,width,ite_true,ite_false,Bool.false_eq_true,Bool.not_false,Bool.not_true,show ∀ n : Nat, n+7=1+(n+6) by omega,rep_add O 1,show ∀ n : Nat, n+6=1+(n+5) by omega] <;> rfl

theorem restore (v : Bool) (k : Nat) (T : List Bool) :
    run0 (table v) (width v*k+8+(if v then 28 else 30))
      ⟨4,rep O (width v*k+7) ++ [false,true,false],false::true::true::T⟩ =
    some ⟨5,[true,true],frame v ++ rep Z (width v*k) ++ digit v true ++ T⟩ := by
  have a := sweepL (table v) 4 [] [] O Z 1 (by intro L R; cases v <;> rfl) (width v*k+7) [false,true,false] (false::true::true::T)
  simp only [List.nil_append,Nat.one_mul] at a
  have b : run0 (table v) 1 ⟨4,[false,true,false],rep Z (width v*k+7) ++ false::true::true::T⟩ =
      some ⟨5,[true,false],true::(rep Z (width v*k+7) ++ false::true::true::T)⟩ := by cases v <;> rfl
  -- move the last zero of the eight-cell frame across the arbitrary carry run
  have E (n : Nat) : rep Z (n+7) ++ false::true::true::T = rep Z 8 ++ (rep Z n ++ true::true::T) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change false::(rep Z (n+7) ++ false::true::true::T) = rep Z 8 ++ (false::(rep Z n ++ true::true::T))
      rw [ih]
      rfl
  rw [E] at a b
  have c : run0 (table v) (if v then 28 else 30) ⟨5,[true,false],true::(rep Z 8 ++ (rep Z (width v*k) ++ true::true::T))⟩ =
      some ⟨5,[true,true],frame v ++ rep Z (width v*k) ++ digit v true ++ T⟩ := by
    have rot (n : Nat) : false::(rep Z n ++ true::true::T) = rep Z n ++ false::true::true::T := by
      induction n with
      | zero => rfl
      | succ n ih => change false::false::(rep Z n ++ true::true::T) = false::(rep Z n ++ false::true::true::T); rw [ih]
    cases v
    · have h : run0 (table false) 30 ⟨5,[true,false],true::(rep Z 8 ++ (rep Z (width false*k) ++ true::true::T))⟩ =
        some ⟨5,[true,true],frame false ++ (false::(rep Z (width false*k) ++ true::true::T))⟩ := by rfl
      rw [rot] at h
      simpa only [List.append_assoc,digit,ite_false,Bool.false_eq_true,List.cons_append,List.nil_append] using h
    · have h : run0 (table true) 28 ⟨5,[true,false],true::(rep Z 8 ++ (rep Z (width true*k) ++ true::true::T))⟩ =
        some ⟨5,[true,true],frame true ++ (false::false::(rep Z (width true*k) ++ true::true::T))⟩ := by rfl
      rw [rot] at h
      have rot2 (n : Nat) : false::(rep Z n ++ false::true::true::T) = rep Z n ++ false::false::true::true::T := by
        induction n with
        | zero => rfl
        | succ n ih => change false::false::(rep Z n ++ false::true::true::T) = false::(rep Z n ++ false::false::true::true::T); rw [ih]
      rw [rot2] at h
      simpa only [List.append_assoc,digit,ite_true,List.cons_append,List.nil_append] using h
  have H := join0 (join0 a b) c
  rw [show width v*k+7+1+(if v then 28 else 30)=width v*k+8+(if v then 28 else 30) by omega] at H
  exact H

theorem enc_carry (v : Bool) (k : Nat) (T : List Bool) :
    rep Z (width v*(k+1)) ++ T = rep Z (width v*k) ++ digit v false ++ T := by
  rw [Nat.mul_succ,rep_add,List.append_assoc]
  simp only [List.append_assoc]
  cases v <;> rfl

theorem total (v : Bool) (bs : List Bool) (k : Nat) :
    run0 (table v) (width v*k+2*width v*carries bs+(if v then 15 else 14)+(if v then 28 else 30)) (scanCfg v k (enc v bs)) =
    some ⟨5,[true,true],frame v ++ rep Z (width v*k) ++ enc v (bump bs)⟩ := by
  induction bs generalizing k with
  | nil =>
    have H := join0 (scan_blank v k) (restore v k [])
    rw [show (if v then 7 else 6)+(width v*k+8+(if v then 28 else 30))=width v*k+2*width v*carries []+(if v then 15 else 14)+(if v then 28 else 30) by cases v <;> simp [carries] <;> omega] at H
    simpa only [enc,bump,List.append_nil] using H
  | cons b bs ih =>
    cases b
    · have H := join0 (scan_zero v k (enc v bs)) (restore v k (enc v bs))
      rw [show (if v then 7 else 6)+(width v*k+8+(if v then 28 else 30))=width v*k+2*width v*carries (false::bs)+(if v then 15 else 14)+(if v then 28 else 30) by cases v <;> simp [carries] <;> omega] at H
      simpa only [enc,bump,List.append_assoc] using H
    · have H := join0 (scan_one v k (enc v bs)) (ih (k+1))
      have E : width v+ (width v*(k+1)+2*width v*carries bs+(if v then 15 else 14)+(if v then 28 else 30)) =
          width v*k+2*width v*carries (true::bs)+(if v then 15 else 14)+(if v then 28 else 30) := by
        cases v <;> simp [width,carries,Nat.mul_add] <;> omega
      rw [E,List.append_assoc,enc_carry] at H
      simpa only [enc,bump,List.append_assoc] using H

def orbit : Nat → List Bool | 0 => [] | n+1 => bump (orbit n)
def family (v : Bool) (n : Nat) : Z0 := cfg v (orbit n)
def entry (v : Bool) : Nat := if v then 27 else 29
def cost (v : Bool) (n : Nat) : Nat := 36+2*width v*carries (orbit n)+(if v then 28 else 30)
theorem first (v : Bool) : run0 (table v) (entry v) ⟨0,[],[]⟩ = some (family v 0) := by cases v <;> rfl
theorem growth (v : Bool) (n : Nat) : run0 (table v) (cost v n) (family v n) = some (family v (n+1)) := by
  have H := join0 (enter v (orbit n)) (total v (orbit n) 0)
  cases v <;> simp only [cost,family,cfg,orbit,Nat.mul_zero,Nat.zero_add,rep,List.nil_append,List.append_nil,List.append_assoc,ite_true,ite_false,Bool.false_eq_true] at H ⊢
  · rw [show 22+(2*width false*carries (orbit n)+14+30)=36+2*width false*carries (orbit n)+30 by omega] at H; exact H
  · rw [show 21+(2*width true*carries (orbit n)+15+28)=36+2*width true*carries (orbit n)+28 by omega] at H; exact H

theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) (family v) (entry v) (cost v) (first v) (by intro n; unfold cost; omega) (growth v) m hm
#print axioms never
end BB6.Agent8Raw54.LFCarryPair
