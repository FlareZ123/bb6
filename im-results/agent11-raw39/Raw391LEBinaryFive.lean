import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw391LEBinaryFive
open BB6Coverage BB6Coverage.Agent31Pump

inductive V where
  | a | b | c | d | e
  deriving DecidableEq

def table (v : V) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨match v with | .a | .b | .c => true | _ => false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨match v with | .a | .b | .c => true | _ => false,true,1⟩)
  | 5,false => some (some (match v with
      | .a => ⟨false,true,0⟩ | .b => ⟨false,true,4⟩ | .c => ⟨true,false,2⟩
      | .d | .e => ⟨false,false,5⟩))
  | 5,true => some (some (match v with
      | .a | .b | .c => ⟨false,false,5⟩ | .d => ⟨true,true,1⟩ | .e => ⟨true,true,4⟩))
  | _,_ => none

def fill : V → Bool | .a | .b | .c => true | _ => false
def quad (v : V) := [fill v,fill v,fill v,fill v]
def core : V → List Bool
  | .a | .b => [true,true,true,true,false]
  | .c => [true,true,true,true,false,false]
  | .d => [false,false,false,true]
  | .e => [false,false,false,false,true,false,true]
def base : V → List Bool
  | .a | .b => [false,true,false]
  | .c => [false,true,false,false]
  | .d => [false,true]
  | .e => [false,false,true,false,true]

def startCost : V → Nat | .a => 7 | .b | .c | .e => 9 | .d => 5
def finishCost : V → Nat | .a => 12 | .b | .c | .e => 14 | .d => 10
abbrev D0 : List Bool := [false,false,false,false]
abbrev D1 : List Bool := [true,false,false,false]
abbrev D2 : List Bool := [false,true,true,true]
abbrev D3 : List Bool := [true,true,true,true]

def frame (v : V) (n : Nat) := rep (quad v) n ++ core v

def C (v : V) (W : List Bool) : Z0 := ⟨4,base v,true::true::W⟩
def S (v : V) (n : Nat) (W : List Bool) : Z0 :=
  ⟨4,W.headD false::frame v n,W.tail⟩

inductive Digits : List Bool → Prop
  | nil : Digits []
  | last : Digits [true]
  | d0 {W} : Digits W → Digits (D0++W)
  | d1 {W} : Digits W → Digits (D1++W)
  | d2 {W} : Digits W → Digits (D2++W)
  | d3 {W} : Digits W → Digits (D3++W)

private theorem prepend (n : Nat) {W} (h : Digits W) : Digits (rep D0 n++W) := by
  induction n with
  | zero => exact h
  | succ n ih => simpa only [rep,List.append_assoc] using Digits.d0 ih

private theorem enter (v : V) (W : List Bool) :
    run0 (table v) (startCost v) (C v W) = some (S v 0 W) := by
  cases v <;> cases W <;> rfl

private theorem carry (v : V) (n : Nat) (W : List Bool) :
    run0 (table v) 4 (S v n (D3++W)) = some (S v (n+1) W) := by
  cases v <;> cases W <;> rfl

private theorem sweepOne (v : V) (L R : List Bool) :
    run0 (table v) 4 ⟨5,quad v++L,R⟩ = some ⟨5,L,D0++R⟩ := by
  cases v <;> rfl

private theorem finish (v : V) (R : List Bool) :
    run0 (table v) (finishCost v) ⟨5,core v,R⟩ = some (C v R) := by
  cases v <;> rfl

private theorem sweep (v : V) (n : Nat) (R : List Bool) :
    run0 (table v) (4*n+finishCost v) ⟨5,frame v n,R⟩ = some (C v (rep D0 n++R)) := by
  have H := sweepL (table v) 5 [] [] (quad v) D0 4 (by simpa only [List.nil_append] using sweepOne v) n (core v) R
  simpa only [frame,List.nil_append] using join0 H (finish v (rep D0 n++R))

private theorem zeroHead (v : V) (n : Nat) (R : List Bool) :
    run0 (table v) 1 (S v n (false::R)) = some ⟨5,frame v n,true::R⟩ := by
  cases v <;> rfl

private theorem emptyHead (v : V) (n : Nat) :
    run0 (table v) 1 (S v n []) = some ⟨5,frame v n,[true]⟩ := by
  cases v <;> rfl

private theorem special (v : V) (n : Nat) (W : List Bool) :
    run0 (table v) 9 (S v n (D1++W)) = some ⟨5,frame v n,D2++W⟩ := by
  cases v <;> rfl

private theorem terminal (v : V) (n : Nat) :
    run0 (table v) 9 (S v n [true]) = some ⟨5,frame v n,D2⟩ := by
  cases v <;> rfl

private theorem reset (v : V) (n : Nat) (R : List Bool) :
    ∃ k, 0 < k ∧ run0 (table v) k ⟨5,frame v n,R⟩ = some (S v 0 (rep D0 n++R)) := by
  refine ⟨4*n+finishCost v+startCost v,?_,join0 (sweep v n R) (enter v _)⟩
  cases v <;> simp [finishCost,startCost] <;> omega

theorem nextVisit (v : V) (n : Nat) {W} (h : Digits W) :
    ∃ k j T, 0 < k ∧ Digits T ∧ run0 (table v) k (S v n W) = some (S v j T) := by
  cases h with
  | nil =>
    obtain ⟨k,hk,hr⟩ := reset v n [true]
    exact ⟨1+k,0,_,by omega,prepend n .last,join0 (emptyHead v n) hr⟩
  | last =>
    obtain ⟨k,hk,hr⟩ := reset v n D2
    exact ⟨9+k,0,_,by omega,prepend n (.d2 .nil),join0 (terminal v n) hr⟩
  | d0 h =>
    obtain ⟨k,hk,hr⟩ := reset v n (D1++_)
    exact ⟨1+k,0,_,by omega,prepend n (.d1 h),join0 (zeroHead v n _) hr⟩
  | d1 h =>
    obtain ⟨k,hk,hr⟩ := reset v n (D2++_)
    exact ⟨9+k,0,_,by omega,prepend n (.d2 h),join0 (special v n _) hr⟩
  | d2 h =>
    obtain ⟨k,hk,hr⟩ := reset v n (D3++_)
    exact ⟨1+k,0,_,by omega,prepend n (.d3 h),join0 (zeroHead v n _) hr⟩
  | d3 h => exact ⟨4,n+1,_,by decide,h,carry v n _⟩

def entryCost : V → Nat | .a => 27 | .b => 31 | .c => 31 | .d => 7 | .e => 30
def entryWord : V → List Bool | .a | .b | .c => [true] | .d | .e => []
private theorem entry (v : V) : run0 (table v) (entryCost v) ⟨0,[],[]⟩ = some (C v (entryWord v)) := by
  cases v <;> rfl
private theorem entryDigits (v : V) : Digits (entryWord v) := by
  cases v <;> first | exact Digits.last | exact Digits.nil

theorem live (v : V) (n : Nat) : ∃ k i W, n ≤ k ∧ Digits W ∧ run0 (table v) k ⟨0,[],[]⟩ = some (S v i W) := by
  induction n with
  | zero => exact ⟨_,0,_,Nat.zero_le _,entryDigits v,join0 (entry v) (enter v _)⟩
  | succ n ih =>
    obtain ⟨k,i,W,hk,hd,hr⟩ := ih
    obtain ⟨t,j,T,ht,hs,he⟩ := nextVisit v i hd
    exact ⟨k+t,j,T,by omega,hs,join0 hr he⟩

theorem never (v : V) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  intro n
  obtain ⟨t,i,W,ht,_,hr⟩ := live v n
  have hz : (BB6Coverage.Agent50Zipper.zrun (table v) t start).map project = some (S v i W) :=
    (run_project (table v) t start).trans hr
  cases h : BB6Coverage.Agent50Zipper.zrun (table v) t start with
  | none => simp [h] at hz
  | some z =>
    have H := BB6Coverage.Agent50Zipper.zrun_sound (table v) m hm t start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms nextVisit
#print axioms never
end BB6.Agent11Raw391LEBinaryFive
