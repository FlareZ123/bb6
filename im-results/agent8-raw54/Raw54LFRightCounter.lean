import Raw54Return
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.LFRightCounter
open BB6Coverage BB6Coverage.Agent31Pump

inductive Kind where
  | k9
  | k11
  | k12
  | k13
  | k15
  | k55
  | k57
  | k58
  | k70
  | k106
  | k109
  | k111
  | k112
  deriving DecidableEq

def c1 : Kind → Move
  | .k9 => ⟨false,false,5⟩
  | .k11 => ⟨true,true,2⟩
  | .k12 => ⟨true,true,5⟩
  | .k13 => ⟨true,true,5⟩
  | .k15 => ⟨true,true,2⟩
  | .k55 => ⟨false,false,5⟩
  | .k57 => ⟨true,true,2⟩
  | .k58 => ⟨true,true,5⟩
  | .k70 => ⟨true,true,5⟩
  | .k106 => ⟨true,true,5⟩
  | .k109 => ⟨false,false,5⟩
  | .k111 => ⟨true,true,2⟩
  | .k112 => ⟨true,true,5⟩

def f0 : Kind → Move
  | .k9 => ⟨false,false,1⟩
  | .k11 => ⟨false,false,1⟩
  | .k12 => ⟨false,false,1⟩
  | .k13 => ⟨false,false,1⟩
  | .k15 => ⟨false,false,1⟩
  | .k55 => ⟨false,true,5⟩
  | .k57 => ⟨false,true,5⟩
  | .k58 => ⟨false,true,5⟩
  | .k70 => ⟨true,false,1⟩
  | .k106 => ⟨true,true,2⟩
  | .k109 => ⟨true,true,5⟩
  | .k111 => ⟨true,true,5⟩
  | .k112 => ⟨true,true,5⟩

def f1 : Kind → Move
  | .k9 => ⟨true,true,1⟩
  | .k11 => ⟨true,true,1⟩
  | .k12 => ⟨true,true,1⟩
  | .k13 => ⟨true,true,2⟩
  | .k15 => ⟨true,true,5⟩
  | .k55 => ⟨true,true,1⟩
  | .k57 => ⟨true,true,1⟩
  | .k58 => ⟨true,true,1⟩
  | .k70 => ⟨true,true,1⟩
  | .k106 => ⟨true,true,1⟩
  | .k109 => ⟨true,true,1⟩
  | .k111 => ⟨true,true,1⟩
  | .k112 => ⟨true,true,1⟩

def anchor : Kind → List Bool
  | .k9 => [true,false,true,true,false,true]
  | .k11 => [true,false,true,true,false,true]
  | .k12 => [true,false,true,true,false,true]
  | .k13 => [true,false,true,true,false,true]
  | .k15 => [true,false,true,true,false,true]
  | .k55 => [true,false,true,true,false]
  | .k57 => [true,false,true,true,false]
  | .k58 => [true,false,true,true,false]
  | .k70 => [true,false,true,true,true,true]
  | .k106 => [true,false,true,true,true]
  | .k109 => [true,false,true,true,true]
  | .k111 => [true,false,true,true,true]
  | .k112 => [true,false,true,true,true]

def entry : Kind → Nat
  | .k9 => 32
  | .k11 => 32
  | .k12 => 32
  | .k13 => 36
  | .k15 => 36
  | .k55 => 26
  | .k57 => 26
  | .k58 => 26
  | .k70 => 28
  | .k106 => 26
  | .k109 => 26
  | .k111 => 26
  | .k112 => 26

def prefixCost : Kind → Nat
  | .k9 => 4
  | .k11 => 4
  | .k12 => 4
  | .k13 => 6
  | .k15 => 6
  | .k55 => 4
  | .k57 => 4
  | .k58 => 4
  | .k70 => 4
  | .k106 => 4
  | .k109 => 4
  | .k111 => 4
  | .k112 => 4

def scanCost : Kind → Nat
  | .k9 => 6
  | .k11 => 2
  | .k12 => 3
  | .k13 => 2
  | .k15 => 2
  | .k55 => 6
  | .k57 => 2
  | .k58 => 3
  | .k70 => 3
  | .k106 => 3
  | .k109 => 6
  | .k111 => 2
  | .k112 => 3

def triple : Kind → Bool
  | .k9 => false
  | .k11 => false
  | .k12 => true
  | .k13 => false
  | .k15 => false
  | .k55 => false
  | .k57 => false
  | .k58 => true
  | .k70 => true
  | .k106 => true
  | .k109 => false
  | .k111 => false
  | .k112 => true

def table (v : Kind) : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some (c1 v))
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some (f0 v))
  | 5,true => some (some (f1 v))
  | _,_ => none

def ones (v : Kind) : List Bool := if triple v then [true,true,true] else [true,true]
def zeros (v : Kind) : List Bool := if triple v then [false,false,false] else [false,false]
def width (v : Kind) : Nat := if triple v then 3 else 2

def enc (v : Kind) : List Bool → List Bool
  | [] => [true,true]
  | b::bs => b::b::(if triple v then false::enc v bs else enc v bs)
def headBit (bs : List Bool) : Bool := bs.headD true

def cfg (v : Kind) (bs : List Bool) : Z0 := ⟨5,anchor v,[true,false,false] ++ enc v bs⟩
def scanCfg (v : Kind) (k : Nat) (bs : List Bool) : Z0 :=
  ⟨2,headBit bs::(rep (ones v) k ++ [true,true,false] ++ anchor v),(enc v bs).tail⟩
def bump : List Bool → List Bool
  | [] => [false]
  | false::bs => true::bs
  | true::bs => false::bump bs

theorem first (v : Kind) : run0 (table v) (entry v) ⟨0,[],[]⟩ = some (cfg v []) := by cases v <;> rfl

theorem prefixStep (v : Kind) (bs : List Bool) :
    run0 (table v) (prefixCost v) (cfg v bs) = some (scanCfg v 0 bs) := by
  cases v <;> cases bs <;> rfl

theorem scanOne (v : Kind) (k : Nat) (bs : List Bool) :
    run0 (table v) (scanCost v) (scanCfg v k (true::bs)) = some (scanCfg v (k+1) bs) := by
  cases v <;> cases bs <;> first | rfl | (cases k <;> rfl)

theorem scanSentinel (v : Kind) (k : Nat) :
    run0 (table v) (scanCost v) (scanCfg v k []) =
      some ⟨2,false::(rep (ones v) (k+1) ++ [true,true,false] ++ anchor v),[]⟩ := by cases v <;> first | rfl | (cases k <;> rfl)

theorem scanZero (v : Kind) (k : Nat) (bs : List Bool) :
    run0 (table v) 1 (scanCfg v k (false::bs)) =
      some ⟨3,[false,false] ++ (rep (ones v) k ++ [true,true,false] ++ anchor v),if triple v then false::enc v bs else enc v bs⟩ := by cases v <;> rfl

theorem enc_zeros (v : Kind) (k : Nat) (bs : List Bool) :
    enc v (List.replicate k false ++ bs) = rep (zeros v) k ++ enc v bs := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ,List.cons_append,enc,ih,rep]
    cases v <;> rfl

theorem rotTrue (v : Kind) (k : Nat) (L : List Bool) :
    rep (ones v) k ++ (true::true::L) = true::true::(rep (ones v) k ++ L) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rep,List.append_assoc]
    rw [ih]
    cases v <;> rfl

theorem rotZero (v : Kind) (k : Nat) (L : List Bool) :
    rep (zeros v) k ++ (false::false::L) = false::false::(rep (zeros v) k ++ L) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rep,List.append_assoc]
    rw [ih]
    cases v <;> rfl

theorem finish (v : Kind) (k : Nat) (R : List Bool) :
    run0 (table v) (5+width v*k) ⟨3,[false,false] ++ (rep (ones v) k ++ [true,true,false] ++ anchor v),R⟩ =
      some ⟨5,anchor v,[true,false,false] ++ rep (zeros v) k ++ true::true::R⟩ := by
  have a : run0 (table v) 2 ⟨3,[false,false] ++ (rep (ones v) k ++ [true,true,false] ++ anchor v),R⟩ =
      some ⟨3,rep (ones v) k ++ [true,true,false] ++ anchor v,true::true::R⟩ := by cases v <;> rfl
  have b : run0 (table v) 2 ⟨3,rep (ones v) k ++ [true,true,false] ++ anchor v,true::true::R⟩ =
      some ⟨4,rep (ones v) k ++ false::anchor v,false::false::true::true::R⟩ := by
    rw [List.append_assoc]
    change run0 (table v) 2 ⟨3,rep (ones v) k ++ (true::true::false::anchor v),true::true::R⟩ = _
    rw [rotTrue]
    cases v <;> rfl
  have c := sweepL (table v) 4 [] [] (ones v) (zeros v) (width v) (by intro L R; cases v <;> rfl) k (false::anchor v) (false::false::true::true::R)
  have d : run0 (table v) 1 ⟨4,false::anchor v,rep (zeros v) k ++ false::false::true::true::R⟩ =
      some ⟨5,anchor v,true::(rep (zeros v) k ++ false::false::true::true::R)⟩ := by cases v <;> rfl
  have H := join0 (join0 (join0 a b) c) d
  rw [show 2+2+width v*k+1 = 5+width v*k by omega] at H
  rw [rotZero] at H
  exact H

theorem scan (v : Kind) (bs : List Bool) (k : Nat) :
    ∃ t, 0<t ∧ run0 (table v) t (scanCfg v k bs) = some (cfg v (List.replicate k false ++ bump bs)) := by
  induction bs generalizing k with
  | nil =>
    have a := scanSentinel v k
    have b : run0 (table v) 1 ⟨2,false::(rep (ones v) (k+1) ++ [true,true,false] ++ anchor v),[]⟩ =
      some ⟨3,[false,false] ++ (rep (ones v) (k+1) ++ [true,true,false] ++ anchor v),[]⟩ := by cases v <;> rfl
    have H := join0 (join0 a b) (finish v (k+1) [])
    refine ⟨scanCost v+1+(5+width v*(k+1)),by omega,?_⟩
    unfold cfg
    rw [show List.replicate k false ++ bump [] = List.replicate (k+1) false ++ [] by rw [List.replicate_succ']; simp [bump]]
    rw [enc_zeros]
    simpa only [enc,List.append_assoc] using H
  | cons b bs ih =>
    cases b
    · have H := join0 (scanZero v k bs) (finish v k (if triple v then false::enc v bs else enc v bs))
      refine ⟨1+(5+width v*k),by omega,?_⟩
      unfold cfg
      rw [enc_zeros]
      simp only [bump,enc,List.append_assoc] at H ⊢
      exact H
    · obtain ⟨t,ht,hr⟩ := ih (k+1)
      refine ⟨scanCost v+t,by omega,?_⟩
      have H := join0 (scanOne v k bs) hr
      rw [List.replicate_succ',List.append_assoc] at H
      exact H

def orbit : Nat → List Bool
  | 0 => []
  | n+1 => bump (orbit n)
def family (v : Kind) (n : Nat) : Z0 := cfg v (orbit n)
theorem family_next (v : Kind) (n : Nat) :
    ∃ t, 0<t ∧ run0 (table v) t (family v n) = some (family v (n+1)) := by
  obtain ⟨t,ht,h⟩ := scan v (orbit n) 0
  exact ⟨prefixCost v+t,by omega,join0 (prefixStep v (orbit n)) h⟩
theorem never (v : Kind) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  BB6.Agent8Raw54.never_of_returns (table v) (family v) (entry v) (first v) (family_next v) m hm
#print axioms never
end BB6.Agent8Raw54.LFRightCounter
