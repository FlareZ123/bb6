import Raw54Return
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.LFCounter10
open BB6Coverage BB6Coverage.Agent31Pump

inductive Kind where
  | k4
  | k16
  | k19
  | k20
  | k22
  | k33
  | k42
  | k45
  | k47
  | k48
  | k53
  | k79
  | k81
  deriving DecidableEq

def a1 : Kind → Option (Option Move)
  | .k4 => some (some ⟨false,true,1⟩)
  | .k16 => some (some ⟨false,true,1⟩)
  | .k19 => some (some ⟨false,true,1⟩)
  | .k20 => some (some ⟨false,true,1⟩)
  | .k22 => some (some ⟨false,true,1⟩)
  | .k33 => none
  | .k42 => some (some ⟨false,true,1⟩)
  | .k45 => none
  | .k47 => none
  | .k48 => none
  | .k53 => some (some ⟨false,true,1⟩)
  | .k79 => some (some ⟨false,true,1⟩)
  | .k81 => some (some ⟨false,true,1⟩)

def b1 : Kind → Option (Option Move)
  | .k4 => none
  | .k16 => none
  | .k19 => none
  | .k20 => none
  | .k22 => none
  | .k33 => some (some ⟨false,true,1⟩)
  | .k42 => none
  | .k45 => some (some ⟨true,true,0⟩)
  | .k47 => some (some ⟨true,true,0⟩)
  | .k48 => some (some ⟨true,true,0⟩)
  | .k53 => none
  | .k79 => none
  | .k81 => none

def c1 : Kind → Move
  | .k4 => ⟨true,true,5⟩
  | .k16 => ⟨false,true,5⟩
  | .k19 => ⟨true,true,2⟩
  | .k20 => ⟨true,true,5⟩
  | .k22 => ⟨true,true,2⟩
  | .k33 => ⟨false,true,5⟩
  | .k42 => ⟨true,true,5⟩
  | .k45 => ⟨false,false,1⟩
  | .k47 => ⟨true,true,1⟩
  | .k48 => ⟨true,true,2⟩
  | .k53 => ⟨true,true,5⟩
  | .k79 => ⟨true,true,5⟩
  | .k81 => ⟨true,true,5⟩

def f0 : Kind → Move
  | .k4 => ⟨false,false,0⟩
  | .k16 => ⟨false,true,0⟩
  | .k19 => ⟨false,true,0⟩
  | .k20 => ⟨false,true,0⟩
  | .k22 => ⟨false,true,0⟩
  | .k33 => ⟨false,true,1⟩
  | .k42 => ⟨false,true,2⟩
  | .k45 => ⟨false,true,5⟩
  | .k47 => ⟨false,true,5⟩
  | .k48 => ⟨false,true,5⟩
  | .k53 => ⟨false,true,5⟩
  | .k79 => ⟨true,true,0⟩
  | .k81 => ⟨true,true,0⟩

def f1 : Kind → Move
  | .k4 => ⟨true,true,0⟩
  | .k16 => ⟨false,false,0⟩
  | .k19 => ⟨false,true,5⟩
  | .k20 => ⟨true,true,2⟩
  | .k22 => ⟨true,true,5⟩
  | .k33 => ⟨false,false,0⟩
  | .k42 => ⟨true,true,0⟩
  | .k45 => ⟨false,true,1⟩
  | .k47 => ⟨false,true,1⟩
  | .k48 => ⟨false,true,1⟩
  | .k53 => ⟨true,true,0⟩
  | .k79 => ⟨false,false,2⟩
  | .k81 => ⟨true,true,0⟩

def anchor : Kind → List Bool
  | .k4 => [true,false,true,false,true,true]
  | .k16 => [false,false,true,true,false]
  | .k19 => [false,false,false,false,false]
  | .k20 => [false,true,true,false,false]
  | .k22 => [false,true,true,false,false]
  | .k33 => [false,false,true,true,false]
  | .k42 => [true,true,true,false,true,false,true,false]
  | .k45 => [false,false]
  | .k47 => [false,false]
  | .k48 => [false,false]
  | .k53 => [true,false,false,false,true,true,false,true,true,true,false]
  | .k79 => [true,true,true,false,true]
  | .k81 => [true,false,true]

def entry : Kind → Nat
  | .k4 => 30
  | .k16 => 26
  | .k19 => 24
  | .k20 => 24
  | .k22 => 24
  | .k33 => 26
  | .k42 => 37
  | .k45 => 29
  | .k47 => 29
  | .k48 => 29
  | .k53 => 60
  | .k79 => 42
  | .k81 => 30

def prefixCost : Kind → Nat
  | .k4 => 3
  | .k16 => 3
  | .k19 => 3
  | .k20 => 3
  | .k22 => 3
  | .k33 => 3
  | .k42 => 3
  | .k45 => 3
  | .k47 => 3
  | .k48 => 3
  | .k53 => 3
  | .k79 => 5
  | .k81 => 3

def scanCost : Kind → Nat
  | .k4 => 4
  | .k16 => 4
  | .k19 => 2
  | .k20 => 2
  | .k22 => 2
  | .k33 => 4
  | .k42 => 4
  | .k45 => 6
  | .k47 => 4
  | .k48 => 2
  | .k53 => 4
  | .k79 => 6
  | .k81 => 4

def quad : Kind → Bool
  | .k4 => true
  | .k16 => false
  | .k19 => false
  | .k20 => false
  | .k22 => false
  | .k33 => false
  | .k42 => true
  | .k45 => true
  | .k47 => true
  | .k48 => false
  | .k53 => true
  | .k79 => true
  | .k81 => true

def initial : Kind → List Bool
  | .k4 => []
  | .k16 => []
  | .k19 => []
  | .k20 => []
  | .k22 => []
  | .k33 => []
  | .k42 => []
  | .k45 => [false]
  | .k47 => [false]
  | .k48 => [false,false]
  | .k53 => []
  | .k79 => [false]
  | .k81 => [false]

def table (v : Kind) : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => a1 v
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => b1 v
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some (c1 v))
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some (f0 v))
  | 5,true => some (some (f1 v))
  | _,_ => none

def ones (v : Kind) : List Bool := if quad v then [true,true,true,true] else [true,true]
def zeros (v : Kind) : List Bool := if quad v then [false,false,false,false] else [false,false]
def width (v : Kind) : Nat := if quad v then 4 else 2

def enc (v : Kind) : List Bool → List Bool
  | [] => [true,true]
  | b::bs => b::b::(if quad v then false::false::enc v bs else enc v bs)
def headBit (bs : List Bool) : Bool := bs.headD true

def cfg (v : Kind) (bs : List Bool) : Z0 := ⟨5,anchor v,[true,false] ++ enc v bs⟩
def scanCfg (v : Kind) (k : Nat) (bs : List Bool) : Z0 :=
  ⟨2,headBit bs::(rep (ones v) k ++ [true,false] ++ anchor v),(enc v bs).tail⟩
def bump : List Bool → List Bool
  | [] => [false]
  | false::bs => true::bs
  | true::bs => false::bump bs

theorem first (v : Kind) : run0 (table v) (entry v) ⟨0,[],[]⟩ = some (cfg v (initial v)) := by cases v <;> rfl

theorem prefixStep (v : Kind) (bs : List Bool) :
    run0 (table v) (prefixCost v) (cfg v bs) = some (scanCfg v 0 bs) := by
  cases v <;> cases bs <;> rfl

theorem scanOne (v : Kind) (k : Nat) (bs : List Bool) :
    run0 (table v) (scanCost v) (scanCfg v k (true::bs)) = some (scanCfg v (k+1) bs) := by
  cases v <;> cases bs <;> first | rfl | (cases k <;> rfl)

theorem scanSentinel (v : Kind) (k : Nat) :
    run0 (table v) (scanCost v) (scanCfg v k []) =
      some ⟨2,false::(rep (ones v) (k+1) ++ [true,false] ++ anchor v),[]⟩ := by cases v <;> first | rfl | (cases k <;> rfl)

theorem scanZero (v : Kind) (k : Nat) (bs : List Bool) :
    run0 (table v) 1 (scanCfg v k (false::bs)) =
      some ⟨3,[false,false] ++ (rep (ones v) k ++ [true,false] ++ anchor v),if quad v then false::false::enc v bs else enc v bs⟩ := by cases v <;> rfl

theorem enc_zeros (v : Kind) (k : Nat) (bs : List Bool) :
    enc v (List.replicate k false ++ bs) = rep (zeros v) k ++ enc v bs := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ,List.cons_append,enc,ih,rep]
    cases v <;> rfl

theorem rotTrue (v : Kind) (k : Nat) (L : List Bool) :
    rep (ones v) k ++ (true::L) = true::(rep (ones v) k ++ L) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rep,List.append_assoc]
    rw [ih]
    cases v <;> rfl

theorem rotZero (v : Kind) (k : Nat) (L : List Bool) :
    rep (zeros v) k ++ (false::L) = false::(rep (zeros v) k ++ L) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rep,List.append_assoc]
    rw [ih]
    cases v <;> rfl

theorem finish (v : Kind) (k : Nat) (R : List Bool) :
    run0 (table v) (4+width v*k) ⟨3,[false,false] ++ (rep (ones v) k ++ [true,false] ++ anchor v),R⟩ =
      some ⟨5,anchor v,[true,false] ++ rep (zeros v) k ++ true::true::R⟩ := by
  have a : run0 (table v) 2 ⟨3,[false,false] ++ (rep (ones v) k ++ [true,false] ++ anchor v),R⟩ =
      some ⟨3,rep (ones v) k ++ [true,false] ++ anchor v,true::true::R⟩ := by cases v <;> rfl
  have b : run0 (table v) 1 ⟨3,rep (ones v) k ++ [true,false] ++ anchor v,true::true::R⟩ =
      some ⟨4,rep (ones v) k ++ false::anchor v,false::true::true::R⟩ := by
    rw [List.append_assoc]
    change run0 (table v) 1 ⟨3,rep (ones v) k ++ (true::false::anchor v),true::true::R⟩ = _
    rw [rotTrue]
    cases v <;> rfl
  have c := sweepL (table v) 4 [] [] (ones v) (zeros v) (width v) (by intro L R; cases v <;> rfl) k (false::anchor v) (false::true::true::R)
  have d : run0 (table v) 1 ⟨4,false::anchor v,rep (zeros v) k ++ false::true::true::R⟩ =
      some ⟨5,anchor v,true::(rep (zeros v) k ++ false::true::true::R)⟩ := by cases v <;> rfl
  have H := join0 (join0 (join0 a b) c) d
  rw [show 2+1+width v*k+1 = 4+width v*k by omega] at H
  rw [rotZero] at H
  exact H

theorem scan (v : Kind) (bs : List Bool) (k : Nat) :
    ∃ t, 0<t ∧ run0 (table v) t (scanCfg v k bs) = some (cfg v (List.replicate k false ++ bump bs)) := by
  induction bs generalizing k with
  | nil =>
    have a := scanSentinel v k
    have b : run0 (table v) 1 ⟨2,false::(rep (ones v) (k+1) ++ [true,false] ++ anchor v),[]⟩ =
      some ⟨3,[false,false] ++ (rep (ones v) (k+1) ++ [true,false] ++ anchor v),[]⟩ := by cases v <;> rfl
    have H := join0 (join0 a b) (finish v (k+1) [])
    refine ⟨scanCost v+1+(4+width v*(k+1)),by omega,?_⟩
    unfold cfg
    rw [show List.replicate k false ++ bump [] = List.replicate (k+1) false ++ [] by rw [List.replicate_succ']; simp [bump]]
    rw [enc_zeros]
    simpa only [enc,List.append_assoc] using H
  | cons b bs ih =>
    cases b
    · have H := join0 (scanZero v k bs) (finish v k (if quad v then false::false::enc v bs else enc v bs))
      refine ⟨1+(4+width v*k),by omega,?_⟩
      unfold cfg
      rw [enc_zeros]
      simp only [bump,enc,List.append_assoc] at H ⊢
      exact H
    · obtain ⟨t,ht,hr⟩ := ih (k+1)
      refine ⟨scanCost v+t,by omega,?_⟩
      have H := join0 (scanOne v k bs) hr
      rw [List.replicate_succ',List.append_assoc] at H
      exact H

def orbit (v : Kind) : Nat → List Bool
  | 0 => initial v
  | n+1 => bump (orbit v n)
def family (v : Kind) (n : Nat) : Z0 := cfg v (orbit v n)
theorem family_next (v : Kind) (n : Nat) :
    ∃ t, 0<t ∧ run0 (table v) t (family v n) = some (family v (n+1)) := by
  obtain ⟨t,ht,h⟩ := scan v (orbit v n) 0
  exact ⟨prefixCost v+t,by omega,join0 (prefixStep v (orbit v n)) h⟩
theorem never (v : Kind) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  BB6.Agent8Raw54.never_of_returns (table v) (family v) (entry v) (first v) (family_next v) m hm
#print axioms never
end BB6.Agent8Raw54.LFCounter10
