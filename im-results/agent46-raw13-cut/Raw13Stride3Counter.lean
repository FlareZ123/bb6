import Raw13BinarySiblings

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13Stride3Counter
open BB6Coverage BB6Coverage.Agent31Pump
open BB6Coverage.Agent31Pump.Auto (knownRun knownRun_sound extend)

inductive Variant where | zeroLA | oneRA
  deriving DecidableEq

def actionCode : Variant → Nat
  | .zeroLA => 0 | .oneRA => 3

def p (v : Variant) : PartialMachine :=
  FAR.fromCodes [7,14,11,5,2,19,22,0,actionCode v,13,2,24]

def enc : List Bool → List Bool
  | [] => [true]
  | b::xs => b::false::false::enc xs

def inc : List Bool → List Bool
  | [] => [false]
  | false::xs => true::xs
  | true::xs => false::inc xs

def Q : List Bool := [true,true,true]
def Z : List Bool := [false,false,false]
def leftFrame : List Bool := [false,true,true]
def rightFrame : List Bool := [false,true,false]
def RPair : List Bool := [true,false]
def LPair : List Bool := [false,true]
def Ones : List Bool := [true,true]

def E (xs : List Bool) (j : Nat) : Z0 :=
  ⟨4,leftFrame ++ enc xs,rep RPair j ++ Ones⟩

theorem rep_three (b : Bool) (k : Nat) : rep [b] (3*k) = rep [b,b,b] k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 3*(k+1)=3*k+3 by omega]
    simpa only [rep,List.singleton_append,List.cons_append,List.nil_append] using congrArg (fun l => b::b::b::l) ih

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
    run0 (p v) 3 ⟨0,true::false::false::L,R⟩ = some ⟨0,L,Q++R⟩ := by
  cases v <;> rfl

theorem carryEnd (v : Variant) (R : List Bool) :
    run0 (p v) 3 ⟨0,[true],R⟩ = some ⟨0,[],Q++R⟩ := by
  cases v <;> rfl

theorem carry (v : Variant) (xs : List Bool) (k : Nat) (R : List Bool) :
    ∃ cost, 0<cost ∧ run0 (p v) cost ⟨0,enc xs,rep Q k++rightFrame++R⟩ =
      some ⟨4,leftFrame++rep Z k++enc (inc xs),R⟩ := by
  induction xs generalizing k with
  | nil =>
    have h1 := carryEnd v (rep Q k++rightFrame++R)
    have h2 := backNil v (3*(k+1)) R
    rw [rep_three] at h2
    have h2' : run0 (p v) (3*(k+1)+3) ⟨0,[],rep Q (k+1)++rightFrame++R⟩ =
        some ⟨4,leftFrame++rep Z (k+1)++[true],R⟩ := by
      simpa only [Q,Z,rep_three] using h2
    have h1' : run0 (p v) 3 ⟨0,enc [],rep Q k++rightFrame++R⟩ =
        some ⟨0,[],rep Q (k+1)++rightFrame++R⟩ := by
      simpa only [rep,enc,List.append_assoc] using h1
    refine ⟨3+(3*(k+1)+3),by omega,?_⟩
    have h := join0 h1' h2'
    rw [show rep Z (k+1) = rep Z k ++ Z from (rep_snoc Z k).symm] at h
    simpa only [inc,enc,Z,List.append_assoc,List.cons_append,List.nil_append] using h
  | cons b xs ih =>
    cases b with
    | false =>
      have h := back v (3*k) (false::false::enc xs) R
      refine ⟨3*k+3,by omega,?_⟩
      simpa only [enc,inc,rep_three,Q,Z] using h
    | true =>
      have h1 := carryOne v (enc xs) (rep Q k++rightFrame++R)
      have h1' : run0 (p v) 3 ⟨0,enc (true::xs),rep Q k++rightFrame++R⟩ =
          some ⟨0,enc xs,rep Q (k+1)++rightFrame++R⟩ := by
        simpa only [rep,enc,List.append_assoc] using h1
      obtain ⟨cost,hpos,h2⟩ := ih (k+1)
      refine ⟨3+cost,by omega,?_⟩
      have h := join0 h1' h2
      rw [show rep Z (k+1) = rep Z k ++ Z from (rep_snoc Z k).symm] at h
      simpa only [inc,enc,Z,List.append_assoc,List.cons_append,List.nil_append] using h


/-- F0=1LA consumes three tape symbols per binary digit instead of four. -/
def shortCost : Variant → Nat
  | .zeroLA => 3
  | .oneRA => 5

theorem short (v : Variant) (L : List Bool) :
    run0 (p v) (shortCost v) ⟨4,leftFrame++L,Ones⟩ =
      some ⟨0,L,rightFrame++Ones⟩ := by
  cases v <;> rfl

theorem shortRun (v : Variant) (xs : List Bool) :
    ∃ cost, 0<cost ∧ run0 (p v) cost (E xs 0) = some (E (inc xs) 0) := by
  have h1 : run0 (p v) (shortCost v) (E xs 0) = some ⟨0,enc xs,rightFrame++Ones⟩ := by
    simpa only [E,rep,List.nil_append] using short v (enc xs)
  obtain ⟨c,hc,h2⟩ := carry v xs 0 Ones
  refine ⟨shortCost v+c,by omega,?_⟩
  exact join0 h1 (by simpa only [E,rep,List.nil_append,List.append_nil] using h2)

def allowed (z : Z0) : Prop := ∃ xs, z = E xs 0

theorem first (v : Variant) : run0 (p v) 34 ⟨0,[],[]⟩ = some (E [true] 0) := by
  cases v <;> decide

theorem never (v : Variant) (m : Machine) (hm : compatible (p v) m) : NeverHalts m := by
  apply BB6.Agent46Raw13BinarySiblings.never_of_return (p v) allowed 34 (E [true] 0)
    (first v) ⟨[true],rfl⟩ _ m hm
  intro z hz
  obtain ⟨xs,rfl⟩ := hz
  obtain ⟨k,hk,hr⟩ := shortRun v xs
  exact ⟨k,E (inc xs) 0,hk,hr,inc xs,rfl⟩

#print axioms carry
#print axioms shortRun
#print axioms never
end BB6.Agent46Raw13Stride3Counter
