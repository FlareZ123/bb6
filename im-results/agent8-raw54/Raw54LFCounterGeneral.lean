import Raw54Return
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.LFCounterGeneral
open BB6Coverage BB6Coverage.Agent31Pump

inductive Kind where
  | k3
  | k24
  | k30
  | k31
  | k40
  | k41
  | k43
  | k52
  | k54
  | k83
  deriving DecidableEq

def a1 : Kind → Option (Option Move)
  | .k3 => some (some ⟨false,true,0⟩)
  | .k24 => some (some ⟨true,true,1⟩)
  | .k30 => none
  | .k31 => none
  | .k40 => none
  | .k41 => some (some ⟨false,false,2⟩)
  | .k43 => some (some ⟨false,true,2⟩)
  | .k52 => some (some ⟨false,true,4⟩)
  | .k54 => some (some ⟨false,true,4⟩)
  | .k83 => some (some ⟨true,true,1⟩)

def b1 : Kind → Option (Option Move)
  | .k3 => none
  | .k24 => none
  | .k30 => some (some ⟨false,true,0⟩)
  | .k31 => some (some ⟨false,true,0⟩)
  | .k40 => some (some ⟨true,true,0⟩)
  | .k41 => none
  | .k43 => none
  | .k52 => none
  | .k54 => none
  | .k83 => none

def c1 : Kind → Move
  | .k3 => ⟨true,true,5⟩
  | .k24 => ⟨true,true,0⟩
  | .k30 => ⟨true,true,1⟩
  | .k31 => ⟨true,true,1⟩
  | .k40 => ⟨true,true,1⟩
  | .k41 => ⟨true,true,5⟩
  | .k43 => ⟨true,true,5⟩
  | .k52 => ⟨true,true,2⟩
  | .k54 => ⟨true,true,5⟩
  | .k83 => ⟨false,true,5⟩

def f0 : Kind → Move
  | .k3 => ⟨false,false,0⟩
  | .k24 => ⟨false,true,0⟩
  | .k30 => ⟨false,true,1⟩
  | .k31 => ⟨false,true,1⟩
  | .k40 => ⟨false,true,2⟩
  | .k41 => ⟨false,true,2⟩
  | .k43 => ⟨false,true,2⟩
  | .k52 => ⟨false,true,5⟩
  | .k54 => ⟨false,true,5⟩
  | .k83 => ⟨true,true,0⟩

def f1 : Kind → Move
  | .k3 => ⟨true,true,0⟩
  | .k24 => ⟨false,true,0⟩
  | .k30 => ⟨false,false,2⟩
  | .k31 => ⟨true,true,2⟩
  | .k40 => ⟨false,true,2⟩
  | .k41 => ⟨true,true,0⟩
  | .k43 => ⟨true,true,0⟩
  | .k52 => ⟨true,true,0⟩
  | .k54 => ⟨true,true,0⟩
  | .k83 => ⟨false,false,0⟩

def anchor : Kind → List Bool
  | .k3 => [true,true]
  | .k24 => [true,false]
  | .k30 => [false]
  | .k31 => [false]
  | .k40 => [true,false]
  | .k41 => [true,false,true,false,true,false]
  | .k43 => [true,false,true,false,true,false]
  | .k52 => [true,false,true,false,true,true,true,false]
  | .k54 => [true,false,true,true,true,false]
  | .k83 => [true,true,true]

def entry : Kind → Nat
  | .k3 => 30
  | .k24 => 29
  | .k30 => 50
  | .k31 => 46
  | .k40 => 27
  | .k41 => 47
  | .k43 => 45
  | .k52 => 67
  | .k54 => 49
  | .k83 => 28

def initial : Kind → List Bool
  | .k3 => [false]
  | .k24 => []
  | .k30 => [false]
  | .k31 => [false]
  | .k40 => []
  | .k41 => []
  | .k43 => []
  | .k52 => []
  | .k54 => []
  | .k83 => []

def markerN : Kind → Nat
  | .k3 => 2
  | .k24 => 5
  | .k30 => 2
  | .k31 => 2
  | .k40 => 4
  | .k41 => 4
  | .k43 => 4
  | .k52 => 3
  | .k54 => 3
  | .k83 => 3

def width : Kind → Nat
  | .k3 => 4
  | .k24 => 3
  | .k30 => 7
  | .k31 => 7
  | .k40 => 4
  | .k41 => 4
  | .k43 => 4
  | .k52 => 2
  | .k54 => 4
  | .k83 => 2

def prefixCost : Kind → Nat
  | .k3 => 4
  | .k24 => 21
  | .k30 => 4
  | .k31 => 4
  | .k40 => 20
  | .k41 => 24
  | .k43 => 20
  | .k52 => 7
  | .k54 => 7
  | .k83 => 7

def scanCost : Kind → Nat
  | .k3 => 4
  | .k24 => 3
  | .k30 => 25
  | .k31 => 21
  | .k40 => 4
  | .k41 => 4
  | .k43 => 4
  | .k52 => 2
  | .k54 => 4
  | .k83 => 4

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

def ones (v : Kind) : List Bool := rep [true] (width v)
def zeros (v : Kind) : List Bool := rep [false] (width v)
def pad (v : Kind) : List Bool := rep [false] (width v-2)
def marker (v : Kind) : List Bool := true::rep [false] (markerN v)
def anchorBase (v : Kind) : List Bool := rep [true] (markerN v) ++ false::anchor v

def enc (v : Kind) : List Bool → List Bool
  | [] => [true,true]
  | b::bs => b::b::(pad v ++ enc v bs)
def headBit (bs : List Bool) : Bool := bs.headD true

def cfg (v : Kind) (bs : List Bool) : Z0 := ⟨5,anchor v,marker v ++ enc v bs⟩
def scanCfg (v : Kind) (k : Nat) (bs : List Bool) : Z0 :=
  ⟨2,headBit bs::(rep (ones v) k ++ anchorBase v),(enc v bs).tail⟩
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
      some ⟨2,false::(rep (ones v) (k+1) ++ anchorBase v),[]⟩ := by cases v <;> first | rfl | (cases k <;> rfl)

theorem scanZero (v : Kind) (k : Nat) (bs : List Bool) :
    run0 (table v) 1 (scanCfg v k (false::bs)) =
      some ⟨3,[false,false] ++ (rep (ones v) k ++ anchorBase v),pad v ++ enc v bs⟩ := by cases v <;> rfl

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

theorem rotTrueN (v : Kind) (k p : Nat) (L : List Bool) :
    rep (ones v) k ++ (rep [true] p ++ L) = rep [true] p ++ (rep (ones v) k ++ L) := by
  induction p with
  | zero => rfl
  | succ p ih =>
    change rep (ones v) k ++ (true::(rep [true] p ++ L)) = true::(rep [true] p ++ (rep (ones v) k ++ L))
    rw [rotTrue,ih]

theorem rotZeroN (v : Kind) (k p : Nat) (L : List Bool) :
    rep (zeros v) k ++ (rep [false] p ++ L) = rep [false] p ++ (rep (zeros v) k ++ L) := by
  induction p with
  | zero => rfl
  | succ p ih =>
    change rep (zeros v) k ++ (false::(rep [false] p ++ L)) = false::(rep [false] p ++ (rep (zeros v) k ++ L))
    rw [rotZero,ih]

theorem finish (v : Kind) (k : Nat) (R : List Bool) :
    run0 (table v) (3+markerN v+width v*k) ⟨3,[false,false] ++ (rep (ones v) k ++ anchorBase v),R⟩ =
      some ⟨5,anchor v,marker v ++ rep (zeros v) k ++ true::true::R⟩ := by
  have a : run0 (table v) 2 ⟨3,[false,false] ++ (rep (ones v) k ++ anchorBase v),R⟩ =
      some ⟨3,rep (ones v) k ++ anchorBase v,true::true::R⟩ := by cases v <;> rfl
  have b : run0 (table v) (markerN v) ⟨3,rep (ones v) k ++ anchorBase v,true::true::R⟩ =
      some ⟨4,rep (ones v) k ++ false::anchor v,rep [false] (markerN v) ++ true::true::R⟩ := by
    unfold anchorBase
    rw [rotTrueN]
    cases v <;> rfl
  have c := sweepL (table v) 4 [] [] (ones v) (zeros v) (width v) (by intro L R; cases v <;> rfl) k (false::anchor v) (rep [false] (markerN v) ++ true::true::R)
  have d : run0 (table v) 1 ⟨4,false::anchor v,rep (zeros v) k ++ (rep [false] (markerN v) ++ true::true::R)⟩ =
      some ⟨5,anchor v,true::(rep (zeros v) k ++ (rep [false] (markerN v) ++ true::true::R))⟩ := by cases v <;> rfl
  have H := join0 (join0 (join0 a b) c) d
  rw [show 2+markerN v+width v*k+1 = 3+markerN v+width v*k by omega] at H
  rw [rotZeroN] at H
  simpa only [marker,List.append_assoc,List.cons_append] using H

theorem scan (v : Kind) (bs : List Bool) (k : Nat) :
    ∃ t, 0<t ∧ run0 (table v) t (scanCfg v k bs) = some (cfg v (List.replicate k false ++ bump bs)) := by
  induction bs generalizing k with
  | nil =>
    have a := scanSentinel v k
    have b : run0 (table v) 1 ⟨2,false::(rep (ones v) (k+1) ++ anchorBase v),[]⟩ =
      some ⟨3,[false,false] ++ (rep (ones v) (k+1) ++ anchorBase v),[]⟩ := by cases v <;> rfl
    have H := join0 (join0 a b) (finish v (k+1) [])
    refine ⟨scanCost v+1+(3+markerN v+width v*(k+1)),by omega,?_⟩
    unfold cfg
    rw [show List.replicate k false ++ bump [] = List.replicate (k+1) false ++ [] by rw [List.replicate_succ']; simp [bump]]
    rw [enc_zeros]
    simpa only [enc,List.append_assoc] using H
  | cons b bs ih =>
    cases b
    · have H := join0 (scanZero v k bs) (finish v k (pad v ++ enc v bs))
      refine ⟨1+(3+markerN v+width v*k),by omega,?_⟩
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
end BB6.Agent8Raw54.LFCounterGeneral
