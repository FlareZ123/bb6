import Agent46AutoPump
import FastFAR

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13BinarySiblings
open BB6Coverage BB6Coverage.Agent31Pump
open BB6Coverage.Agent31Pump.Auto (knownRun knownRun_sound extend)

inductive Variant where | zeroLA | oneRA | zeroLE | oneLE | oneRC
  deriving DecidableEq

def actionCode : Variant → Nat
  | .zeroLA => 0 | .oneRA => 3 | .zeroLE => 16 | .oneLE => 18 | .oneRC => 11

def p (v : Variant) : PartialMachine :=
  FAR.fromCodes [7,14,11,5,2,19,22,0,actionCode v,13,10,24]

def enc : List Bool → List Bool
  | [] => [true]
  | b::xs => b::false::false::false::enc xs

def inc : List Bool → List Bool
  | [] => [false]
  | false::xs => true::xs
  | true::xs => false::inc xs

def Q : List Bool := [true,true,true,true]
def Z : List Bool := [false,false,false,false]
def leftFrame : List Bool := [false,true,true]
def rightFrame : List Bool := [false,true,false]
def RPair : List Bool := [true,false]
def LPair : List Bool := [false,true]
def Ones : List Bool := [true,true]

def E (xs : List Bool) (j : Nat) : Z0 :=
  ⟨4,leftFrame ++ enc xs,rep RPair j ++ Ones⟩

theorem rep_four (b : Bool) (k : Nat) : rep [b] (4*k) = rep [b,b,b,b] k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 4*(k+1)=4*k+4 by omega]
    simpa only [rep,List.singleton_append,List.cons_append,List.nil_append] using congrArg (fun l => b::b::b::b::l) ih

theorem rep_one_step (v : Variant) (L R : List Bool) :
    run0 (p v) 1 ⟨1,[true]++L,[]++[true]++R⟩ = some ⟨1,[true]++[false]++L,[]++R⟩ := by
  cases v <;> rfl

theorem endB (v : Variant) (L R : List Bool) :
    run0 (p v) 3 ⟨1,true::L,rightFrame++R⟩ = some ⟨4,leftFrame++false::L,R⟩ := by
  cases v <;> rfl

theorem back (v : Variant) (n : Nat) (L R : List Bool) :
    run0 (p v) (n+3) ⟨0,false::L,rep [true] n++rightFrame++R⟩ =
      some ⟨4,leftFrame++rep [false] n++true::L,R⟩ := by
  cases n with
  | zero => cases v <;> rfl
  | succ n =>
    have h1 : run0 (p v) 1 ⟨0,false::L,rep [true] (n+1)++rightFrame++R⟩ =
        some ⟨1,[true,true]++L,rep [true] n++rightFrame++R⟩ := by cases v <;> rfl
    have h2 := sweepR (p v) 1 [true] [] [true] [false] 1 (rep_one_step v) n (true::L) (rightFrame++R)
    have h2' : run0 (p v) n ⟨1,[true,true]++L,rep [true] n++rightFrame++R⟩ =
        some ⟨1,[true]++rep [false] n++true::L,rightFrame++R⟩ := by
      simpa only [Nat.one_mul,List.nil_append,List.cons_append,List.singleton_append,List.append_assoc] using h2
    have h3 := endB v (rep [false] n++true::L) R
    have hh := join0 (join0 h1 h2') h3
    simpa only [rep,List.singleton_append,List.cons_append,List.nil_append,List.append_assoc,show 1+n+3=n+1+3 by omega] using hh

theorem backNil (v : Variant) (n : Nat) (R : List Bool) :
    run0 (p v) (n+3) ⟨0,[],rep [true] n++rightFrame++R⟩ =
      some ⟨4,leftFrame++rep [false] n++[true],R⟩ := by
  have h := back v n [] R
  change run0 (p v) (n+3) ⟨0,[false],rep [true] n++rightFrame++R⟩ = _ at h
  rw [show n+3=(n+2)+1 by omega,run0] at h ⊢
  exact h

theorem carryOne (v : Variant) (L R : List Bool) :
    run0 (p v) 4 ⟨0,true::false::false::false::L,R⟩ = some ⟨0,L,Q++R⟩ := by
  cases v <;> rfl

theorem carryEnd (v : Variant) (R : List Bool) :
    run0 (p v) 4 ⟨0,[true],R⟩ = some ⟨0,[],Q++R⟩ := by
  cases v <;> rfl

theorem carry (v : Variant) (xs : List Bool) (k : Nat) (R : List Bool) :
    ∃ cost, 0<cost ∧ run0 (p v) cost ⟨0,enc xs,rep Q k++rightFrame++R⟩ =
      some ⟨4,leftFrame++rep Z k++enc (inc xs),R⟩ := by
  induction xs generalizing k with
  | nil =>
    have h1 := carryEnd v (rep Q k++rightFrame++R)
    have h2 := backNil v (4*(k+1)) R
    rw [rep_four] at h2
    have h2' : run0 (p v) (4*(k+1)+3) ⟨0,[],rep Q (k+1)++rightFrame++R⟩ =
        some ⟨4,leftFrame++rep Z (k+1)++[true],R⟩ := by
      simpa only [Q,Z,rep_four] using h2
    have h1' : run0 (p v) 4 ⟨0,enc [],rep Q k++rightFrame++R⟩ =
        some ⟨0,[],rep Q (k+1)++rightFrame++R⟩ := by
      simpa only [rep,enc,List.append_assoc] using h1
    refine ⟨4+(4*(k+1)+3),by omega,?_⟩
    have h := join0 h1' h2'
    rw [show rep Z (k+1) = rep Z k ++ Z from (rep_snoc Z k).symm] at h
    simpa only [inc,enc,Z,List.append_assoc,List.cons_append,List.nil_append] using h
  | cons b xs ih =>
    cases b with
    | false =>
      have h := back v (4*k) (false::false::false::enc xs) R
      refine ⟨4*k+3,by omega,?_⟩
      simpa only [enc,inc,rep_four,Q,Z] using h
    | true =>
      have h1 := carryOne v (enc xs) (rep Q k++rightFrame++R)
      have h1' : run0 (p v) 4 ⟨0,enc (true::xs),rep Q k++rightFrame++R⟩ =
          some ⟨0,enc xs,rep Q (k+1)++rightFrame++R⟩ := by
        simpa only [rep,enc,List.append_assoc] using h1
      obtain ⟨cost,hpos,h2⟩ := ih (k+1)
      refine ⟨4+cost,by omega,?_⟩
      have h := join0 h1' h2
      rw [show rep Z (k+1) = rep Z k ++ Z from (rep_snoc Z k).symm] at h
      simpa only [inc,enc,Z,List.append_assoc,List.cons_append,List.nil_append] using h


def growing : Variant → Bool
  | .zeroLA | .oneRA => false
  | _ => true

def rightCost : Variant → Nat
  | .zeroLE => 10 | .oneLE => 6 | .oneRC => 2 | _ => 0

def turnCost : Variant → Nat
  | .zeroLE => 19 | .oneLE => 15 | .oneRC => 11 | _ => 0

def shortCost : Variant → Nat
  | .zeroLA => 3 | .oneRA => 5 | _ => 0

theorem rightOne (v : Variant) (hv : growing v = true) (L R : List Bool) :
    run0 (p v) (rightCost v) ⟨4,leftFrame++L,[]++RPair++R⟩ =
      some ⟨4,leftFrame++Ones++L,[]++R⟩ := by
  cases v <;> simp [growing] at hv <;> rfl

theorem turn (v : Variant) (hv : growing v = true) (L : List Bool) :
    run0 (p v) (turnCost v) ⟨4,leftFrame++L,Ones⟩ =
      some ⟨0,Ones++Ones++Ones++L,[true]⟩ := by
  cases v <;> simp [growing] at hv <;> rfl

theorem leftOne (v : Variant) (L R : List Bool) :
    run0 (p v) 2 ⟨0,[]++Ones++L,[]++R⟩ =
      some ⟨0,[]++L,[]++LPair++R⟩ := by
  cases v <;> rfl

theorem short (v : Variant) (hv : growing v = false) (L : List Bool) :
    run0 (p v) (shortCost v) ⟨4,leftFrame++L,Ones⟩ =
      some ⟨0,L,rightFrame++Ones⟩ := by
  cases v <;> simp [growing] at hv <;> rfl

theorem pairs_align (j : Nat) : rep LPair (j+3)++[true] =
    rightFrame++(rep RPair (j+1)++Ones) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change false::true::(rep LPair (j+3)++[true]) =
      false::true::(rightFrame++(rep RPair (j+1)++Ones))
    exact congrArg (fun x => false::true::x) ih

theorem growRun (v : Variant) (hv : growing v = true) (xs : List Bool) (j : Nat) :
    ∃ cost, 0<cost ∧ run0 (p v) cost (E xs j) = some (E (inc xs) (j+1)) := by
  have h1 := sweepR (p v) 4 leftFrame [] RPair Ones (rightCost v) (rightOne v hv) j (enc xs) Ones
  have h1' : run0 (p v) (rightCost v*j) (E xs j) =
      some ⟨4,leftFrame++rep Ones j++enc xs,Ones⟩ := by
    simpa only [E,List.nil_append] using h1
  have h2 := turn v hv (rep Ones j++enc xs)
  have h2' : run0 (p v) (turnCost v) ⟨4,leftFrame++rep Ones j++enc xs,Ones⟩ =
      some ⟨0,rep Ones (j+3)++enc xs,[true]⟩ := by
    simpa only [rep,List.append_assoc] using h2
  have h3 := sweepL (p v) 0 [] [] Ones LPair 2 (leftOne v) (j+3) (enc xs) [true]
  have h3' : run0 (p v) (2*(j+3)) ⟨0,rep Ones (j+3)++enc xs,[true]⟩ =
      some ⟨0,enc xs,rightFrame++(rep RPair (j+1)++Ones)⟩ := by
    simpa only [List.nil_append,pairs_align] using h3
  obtain ⟨c,hc,h4⟩ := carry v xs 0 (rep RPair (j+1)++Ones)
  have h4' : run0 (p v) c ⟨0,enc xs,rightFrame++(rep RPair (j+1)++Ones)⟩ =
      some (E (inc xs) (j+1)) := by
    simpa only [E,rep,List.nil_append,List.append_nil] using h4
  exact ⟨rightCost v*j+turnCost v+2*(j+3)+c,by omega,join0 (join0 (join0 h1' h2') h3') h4'⟩

theorem shortRun (v : Variant) (hv : growing v = false) (xs : List Bool) :
    ∃ cost, 0<cost ∧ run0 (p v) cost (E xs 0) = some (E (inc xs) 0) := by
  have h1 : run0 (p v) (shortCost v) (E xs 0) = some ⟨0,enc xs,rightFrame++Ones⟩ := by
    simpa only [E,rep,List.nil_append] using short v hv (enc xs)
  obtain ⟨c,hc,h2⟩ := carry v xs 0 Ones
  refine ⟨shortCost v+c,by omega,?_⟩
  exact join0 h1 (by simpa only [E,rep,List.nil_append,List.append_nil] using h2)

open BB6Coverage.Agent50Zipper in
theorem never_of_return (p : PartialMachine) (S : Z0 → Prop) (entry : Nat) (z : Z0)
    (first : run0 p entry ⟨0,[],[]⟩ = some z) (hz : S z)
    (progress : ∀ z, S z → ∃ k z', 0<k ∧ run0 p k z = some z' ∧ S z')
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  have arbitrary : ∀ n, ∃ t w, n ≤ t ∧ run0 p t ⟨0,[],[]⟩ = some w ∧ S w := by
    intro n
    induction n with
    | zero => exact ⟨entry,z,by omega,first,hz⟩
    | succ n ih =>
      obtain ⟨t,w,ht,hr,hw⟩ := ih
      obtain ⟨k,w',hk,hstep,hw'⟩ := progress w hw
      exact ⟨t+k,w',by omega,join0 hr hstep,hw'⟩
  intro n
  obtain ⟨t,w,ht,hr,_⟩ := arbitrary n
  have hw : (zrun p t start).map project = some w := (run_project p t start).trans hr
  cases h : zrun p t start with
  | none => simp [h] at hw
  | some z =>
    have H := zrun_sound p m hm t start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

def allowed (v : Variant) (z : Z0) : Prop :=
  ∃ xs j, (growing v = false → j = 0) ∧ z = E xs j

theorem first (v : Variant) : run0 (p v) 32 ⟨0,[],[]⟩ = some (E [false] 0) := by
  cases v <;> decide

theorem never (v : Variant) (m : Machine) (hm : compatible (p v) m) : NeverHalts m := by
  apply never_of_return (p v) (allowed v) 32 (E [false] 0) (first v) ⟨[false],0,by simp,rfl⟩ _ m hm
  intro z hz
  obtain ⟨xs,j,hj,rfl⟩ := hz
  cases h : growing v with
  | false =>
    have hj0 := hj h
    subst j
    obtain ⟨k,hk,hr⟩ := shortRun v h xs
    exact ⟨k,E (inc xs) 0,hk,hr,inc xs,0,by simp,rfl⟩
  | true =>
    obtain ⟨k,hk,hr⟩ := growRun v h xs j
    exact ⟨k,E (inc xs) (j+1),hk,hr,inc xs,j+1,by simp [h],rfl⟩

#print axioms carry
#print axioms growRun
#print axioms shortRun
#print axioms never
end BB6.Agent46Raw13BinarySiblings
