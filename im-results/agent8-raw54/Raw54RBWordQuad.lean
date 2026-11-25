import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.RBWordQuad
open BB6Coverage BB6Coverage.Agent31Pump

def table (e f : Bool) : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,if e then 4 else 3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => if f then none else some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,if f then 5 else 1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => if f then some (some ⟨false,true,5⟩) else none
  | _,_ => none

def O : List Bool := [true]
def Z : List Bool := [false]
def S : List Bool := [false,true,true,true]
def M : List Bool := [true,true,false,false]
def P : List Bool := [false,true]
def Q : List Bool := [true,true,false,true,true]
def Z5 : List Bool := [false,false,false,false,false]
def Z4 : List Bool := [false,false,false,false]
def O4 : List Bool := [true,true,true,true]
def enc : List Bool → List Bool
  | [] => []
  | b::w => (if b then O4 else Z4) ++ enc w
def bump : List Bool → List Bool
  | [] => [true]
  | false::w => true::w
  | true::w => false::bump w
def carries : List Bool → Nat
  | true::w => carries w + 1
  | _ => 0

def E (k : Nat) (U : List Bool) : Z0 := ⟨4,[],Z5 ++ (rep M k ++ U)⟩
def A (k : Nat) (U : List Bool) : Z0 := ⟨0,P ++ rep S (k+1),false::U⟩
def C (n k : Nat) (U : List Bool) : Z0 := ⟨0,Q ++ (rep O n ++ rep S (k+1)),U⟩

theorem prep (e f : Bool) (U : List Bool) :
    run0 (table e f) 16 ⟨4,[],Z5 ++ U⟩ = some ⟨0,P ++ S,false::U⟩ := by
  cases e <;> cases f <;> rfl

theorem scan (e f : Bool) (k : Nat) (U : List Bool) :
    run0 (table e f) (16+12*k) (E k U) = some (A k U) := by
  have a := prep e f (rep M k ++ U)
  have b := sweepR (table e f) 0 P [false] M S 12 (by intro L R; cases e <;> cases f <;> rfl) k S U
  have H := join0 a b
  simpa only [E,A,List.append_assoc,rep_snoc,rep,List.cons_append,List.nil_append] using H

theorem stack (e f : Bool) (k : Nat) (U : List Bool) :
    run0 (table e f) (10*k) ⟨4,rep S k,Z5 ++ U⟩ = some (E k U) := by
  simpa only [List.nil_append,List.append_nil,List.append_assoc,E] using
    (sweepL (table e f) 4 [] Z5 S M 10 (by intro L R; cases e <;> cases f <;> rfl) k [] U)

theorem finish (e f : Bool) (n : Nat) (L T : List Bool) :
    run0 (table e f) (n+18) ⟨0,P ++ (false::(rep O (n+3) ++ L)),false::false::false::T⟩ =
      some ⟨4,L,rep Z (n+5) ++ (O4 ++ T)⟩ := by
  have a : run0 (table e f) 8 ⟨0,P ++ (false::(rep O (n+3) ++ L)),false::false::false::T⟩ =
      some ⟨4,false::(rep O (n+3) ++ L),false::false::false::true::true::T⟩ := by cases e <;> cases f <;> rfl
  have b : run0 (table e f) 6 ⟨4,false::(rep O (n+3) ++ L),false::false::false::true::true::T⟩ =
      some ⟨4,rep O (n+4) ++ L,false::(O4 ++ T)⟩ := by cases e <;> cases f <;> rfl
  have c := sweepL (table e f) 4 [] [] O Z 1 (by intro L R; cases e <;> cases f <;> rfl) (n+4) L (false::(O4 ++ T))
  simp only [List.nil_append,Nat.one_mul] at c
  have H := join0 (join0 a b) c
  have rot : ∀ n, rep Z (n+4) ++ false::(O4 ++ T) = rep Z (n+5) ++ (O4 ++ T) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      change false::(rep Z (k+4) ++ false::(O4 ++ T)) = false::(rep Z (k+5) ++ (O4 ++ T))
      rw [ih]
  rw [rot,show 8+6+(n+4)=n+18 by omega] at H
  exact H

theorem finish_blank (e f : Bool) (n : Nat) (L : List Bool) :
    run0 (table e f) (n+18) ⟨0,P ++ (false::(rep O (n+3) ++ L)),[]⟩ =
      some ⟨4,L,rep Z (n+5) ++ O4⟩ := by
  have a : run0 (table e f) 8 ⟨0,P ++ (false::(rep O (n+3) ++ L)),[]⟩ =
      some ⟨4,false::(rep O (n+3) ++ L),[false,false,false,true,true]⟩ := by cases e <;> cases f <;> rfl
  have b : run0 (table e f) 8 ⟨0,P ++ (false::(rep O (n+3) ++ L)),[false,false,false]⟩ =
      some ⟨4,false::(rep O (n+3) ++ L),[false,false,false,true,true]⟩ := by cases e <;> cases f <;> rfl
  have H := finish e f n L []
  rw [show n+18=8+(n+10) by omega,run0_add,b] at H
  rw [show n+18=8+(n+10) by omega,run0_add,a]
  simpa only [List.append_nil] using H

theorem phase0 (e f : Bool) (k : Nat) (U : List Bool) :
    run0 (table e f) (34+22*k) (E k (false::false::U)) = some (E k (O4 ++ U)) := by
  have a := scan e f k (false::false::U)
  have b := finish e f 0 (rep S k) U
  have c := stack e f k (O4 ++ U)
  have H := join0 (join0 a b) c
  rw [show 16+12*k+(0+18)+10*k=34+22*k by omega] at H
  exact H

theorem carry_start (e f : Bool) (k : Nat) (U : List Bool) :
    run0 (table e f) 19 (A k (O4 ++ U)) = some (C 2 k U) := by cases e <;> cases f <;> rfl

theorem carry4 (e f : Bool) (n k : Nat) (U : List Bool) :
    run0 (table e f) 28 (C n k (O4 ++ U)) = some (C (n+4) k U) := by cases e <;> cases f <;> rfl

theorem carry_stop (e f : Bool) (n k : Nat) (U : List Bool) :
    run0 (table e f) 7 (C n k (false::U)) =
      some ⟨0,P ++ (false::(rep O (n+3) ++ rep S (k+1))),U⟩ := by cases e <;> cases f <;> rfl

theorem carry_stop_blank (e f : Bool) (n k : Nat) :
    run0 (table e f) 7 (C n k []) =
      some ⟨0,P ++ (false::(rep O (n+3) ++ rep S (k+1))),[]⟩ := by cases e <;> cases f <;> rfl

theorem rep_add (p : List Bool) (a b : Nat) : rep p (a+b) = rep p a ++ rep p b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [show a+1+b=a+b+1 by omega]; simp only [rep,ih,List.append_assoc]

theorem carry_all (e f : Bool) (w : List Bool) (n k : Nat) :
    run0 (table e f) (n+25+32*carries w) (C n k (enc w)) =
      some ⟨4,rep S (k+1),rep Z (n+5) ++ enc (bump w)⟩ := by
  induction w generalizing n with
  | nil =>
    have H := join0 (carry_stop_blank e f n k) (finish_blank e f n (rep S (k+1)))
    simpa only [enc,bump,carries,ite_true,List.append_nil,Nat.mul_zero,Nat.add_zero,show 7+(n+18)=n+25 by omega] using H
  | cons b w ih =>
    cases b
    · have H := join0 (carry_stop e f n k (false::false::false::enc w)) (finish e f n (rep S (k+1)) (enc w))
      simpa only [enc,bump,carries,Z4,List.cons_append,List.nil_append,ite_false,Bool.false_eq_true,ite_true,Nat.mul_zero,Nat.add_zero,List.append_assoc,show 7+(n+18)=n+25 by omega] using H
    · have H := join0 (carry4 e f n k (enc w)) (ih (n+4))
      rw [show n+4+5=n+5+4 by omega,rep_add Z (n+5) 4,show rep Z 4 = Z4 by rfl] at H
      simpa only [enc,bump,carries,ite_true,ite_false,Bool.false_eq_true,List.append_assoc,show 28+(n+4+25+32*carries w)=n+25+32*(carries w+1) by omega] using H

theorem phase1 (e f : Bool) (k : Nat) (w : List Bool) :
    run0 (table e f) (72+22*k+32*carries w) (E k (O4 ++ enc w)) =
      some (E (k+1) (false::false::enc (bump w))) := by
  have a := scan e f k (O4 ++ enc w)
  have b := carry_start e f k (enc w)
  have c := carry_all e f w 2 k
  have d := stack e f (k+1) (false::false::enc (bump w))
  have H := join0 (join0 (join0 a b) c) d
  rw [show 16+12*k+19+(2+25+32*carries w)+10*(k+1)=72+22*k+32*carries w by omega] at H
  exact H

def orbit : Nat → List Bool | 0 => [] | n+1 => bump (orbit n)
def family (n : Nat) : Z0 := E n (O4 ++ enc (orbit n))
def cost (n : Nat) : Nat := 128+44*n+32*carries (orbit n)
theorem first (e f : Bool) : run0 (table e f) 34 ⟨0,[],[]⟩ = some (family 0) := by cases e <;> cases f <;> rfl

theorem growth (e f : Bool) (n : Nat) : run0 (table e f) (cost n) (family n) = some (family (n+1)) := by
  have H := join0 (phase1 e f n (orbit n)) (phase0 e f (n+1) (enc (bump (orbit n))))
  rw [show 72+22*n+32*carries (orbit n)+(34+22*(n+1))=cost n by unfold cost; omega] at H
  exact H

theorem never (e f : Bool) (m : Machine) (hm : compatible (table e f) m) : NeverHalts m :=
  never_of_growth (table e f) family 34 cost (first e f) (by intro n; unfold cost; omega) (growth e f) m hm
#print axioms never
end BB6.Agent8Raw54.RBWordQuad
