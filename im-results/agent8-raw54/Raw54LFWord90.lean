import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.LFWord90
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,true,1⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def P : List Bool := [true,false]
def Q : List Bool := [false,true]
def C : List Bool := [true,true,false,true]
def K : List Bool := [true,false,false,false]
def D0 : List Bool := [false,false,true,false]
def D1 : List Bool := [false,true,false,false]
inductive Word where
  | endd : Bool → Word
  | cons : Bool → Word → Word

def enc : Word → List Bool
  | .endd b => [false,true,!b]
  | .cons b w => (if b then D1 else D0) ++ enc w
def bump : Word → Word
  | .endd false => .endd true
  | .endd true => .cons false (.endd false)
  | .cons false w => .cons true w
  | .cons true w => .cons false (bump w)
def scanCost : Word → Nat
  | .endd false => 8
  | .endd true => 18
  | .cons false _ => 8
  | .cons true w => 10+scanCost w

def cfg (j : Nat) (w : Word) : Z0 := ⟨5,[],rep P (j+1) ++ enc w⟩
def scanCfg (c j : Nat) (R : List Bool) : Z0 := ⟨0,false::false::true::(rep C c ++ rep Q j),R⟩

theorem enter (j : Nat) (w : Word) : run0 table (2*(j+1)) (cfg j w) = some (scanCfg 0 j (enc w)) := by
  have a : run0 table 2 (cfg j w) = some ⟨0,[false,false,true],rep P j ++ enc w⟩ := by rfl
  have b := sweepR table 0 [false,false,true] [] P Q 2 (by intro L R; rfl) j [] (enc w)
  simp only [List.nil_append,List.append_nil,List.cons_append] at b
  have H := join0 a b
  rw [show 2+2*j=2*(j+1) by omega] at H
  exact H

theorem carry (c j : Nat) (T : List Bool) : run0 table 6 (scanCfg c j (D1 ++ T)) = some (scanCfg (c+1) j T) := by rfl
theorem zero (c j : Nat) (T : List Bool) :
    run0 table 8 (scanCfg c j (D0 ++ T)) = some ⟨5,true::(rep C c ++ rep Q j),P ++ D1 ++ T⟩ := by rfl
theorem end0 (c j : Nat) :
    run0 table 8 (scanCfg c j (enc (.endd false))) = some ⟨5,true::(rep C c ++ rep Q j),P ++ enc (.endd true)⟩ := by rfl
theorem end1 (c j : Nat) :
    run0 table 18 (scanCfg c j (enc (.endd true))) = some ⟨5,true::(rep C c ++ rep Q j),P ++ enc (.cons false (.endd false))⟩ := by rfl

theorem shift_words (c : Nat) (T : List Bool) : rep K c ++ (P ++ T) = P ++ (rep D0 c ++ T) := by
  induction c with
  | zero => rfl
  | succ c ih =>
    simp only [rep,List.append_assoc,ih]
    rfl

theorem drain (c j : Nat) (T : List Bool) :
    run0 table (4*c+2*j+2) ⟨5,true::(rep C c ++ rep Q j),P ++ T⟩ =
      some ⟨5,[],rep P (j+2) ++ (rep D0 c ++ T)⟩ := by
  have a := sweepL table 5 [true] [] C K 4 (by intro L R; rfl) c (rep Q j) (P ++ T)
  simp only [List.nil_append,List.cons_append] at a
  rw [shift_words] at a
  have b := sweepL table 5 [true] [] Q P 2 (by intro L R; rfl) j [] (P ++ (rep D0 c ++ T))
  simp only [List.nil_append,List.append_nil,List.cons_append] at b
  have d : run0 table 2 ⟨5,[true],rep P j ++ (P ++ (rep D0 c ++ T))⟩ =
      some ⟨5,[],P ++ (rep P j ++ (P ++ (rep D0 c ++ T)))⟩ := by rfl
  have H := join0 (join0 a b) d
  have e : P ++ (rep P j ++ (P ++ (rep D0 c ++ T))) = rep P (j+2) ++ (rep D0 c ++ T) := by
    simp only [rep,List.append_assoc,← List.append_assoc (rep P j) P,rep_snoc]
  rw [e] at H
  exact H

theorem scan (w : Word) (c j : Nat) :
    run0 table (scanCost w+4*c+2*j+2) (scanCfg c j (enc w)) =
      some ⟨5,[],rep P (j+2) ++ (rep D0 c ++ enc (bump w))⟩ := by
  induction w generalizing c with
  | endd b =>
    cases b
    · have H := join0 (end0 c j) (drain c j (enc (.endd true)))
      rw [show 8+(4*c+2*j+2)=scanCost (.endd false)+4*c+2*j+2 by simp [scanCost]; omega] at H
      exact H
    · have H := join0 (end1 c j) (drain c j (enc (.cons false (.endd false))))
      rw [show 18+(4*c+2*j+2)=scanCost (.endd true)+4*c+2*j+2 by simp [scanCost]; omega] at H
      exact H
  | cons b w ih =>
    cases b
    · have H := join0 (zero c j (enc w)) (drain c j (enc (.cons true w)))
      rw [show 8+(4*c+2*j+2)=scanCost (.cons false w)+4*c+2*j+2 by simp [scanCost]; omega] at H
      exact H
    · have H := join0 (carry c j (enc w)) (ih (c+1))
      rw [show 6+(scanCost w+4*(c+1)+2*j+2)=scanCost (.cons true w)+4*c+2*j+2 by simp [scanCost]; omega] at H
      have eq : rep D0 (c+1) ++ enc (bump w) = rep D0 c ++ enc (bump (.cons true w)) := by
        rw [rep,← rep_snoc]
        simp only [bump,enc,Bool.false_eq_true,ite_false,List.append_assoc]
      rw [eq] at H
      exact H

def orbit : Nat → Word | 0 => .endd false | n+1 => bump (orbit n)
def family (n : Nat) : Z0 := cfg n (orbit n)
def cost (n : Nat) : Nat := 4*n+4+scanCost (orbit n)
theorem first : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have H := join0 (enter n (orbit n)) (scan (orbit n) 0 n)
  rw [show 2*(n+1)+(scanCost (orbit n)+4*0+2*n+2)=cost n by unfold cost; omega] at H
  exact H
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 cost first (by intro n; unfold cost; omega) growth m hm
#print axioms never
end BB6.Agent8Raw54.LFWord90
