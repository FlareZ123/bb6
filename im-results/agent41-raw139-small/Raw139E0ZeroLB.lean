import SparseZipper

namespace BB6Coverage.Agent41Raw139ZeroLB
open Agent50Zipper
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

def table (b : Bool) : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 0, true => some (some ⟨false, b, if b then 3 else 4⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true => some (some ⟨false, true, 2⟩)
  | 2, false => some (some ⟨true, false, 3⟩)
  | 2, true => some (some ⟨false, true, 1⟩)
  | 3, false => some (some ⟨true, false, 0⟩)
  | 3, true => some (some ⟨false, false, 4⟩)
  | 4, false => some (some ⟨false, false, 1⟩)
  | 4, true => some (some ⟨true, false, 5⟩)
  | 5, false => some (some ⟨true, false, 3⟩)
  | _, _ => none
def P : List Bool := [true,false,false,true,false,true,false,true]
def S : List Bool := [false,false,false,true,false,true]
def T1 : List Bool := [true,false,false,true]
def T2 : List Bool := [true,false,true,false,true,false,false,true]
def W (b : Bool) : List Bool := if b then [true,false,true,false,true,false,false,false,false,true,false,true,false,true] else [true,false,false,false,false,true,false,true,false,true]
def U (b : Bool) : List Bool := if b then [true,false,true,true,false,true,false,true,false,true,true,false,true,false] else [true,false,true,true,false,true,true,false,true,false]
def V (b : Bool) : List Bool := if b then [true,true,true,false,true,false,true,false,true,true,false,true,false] else [true,true,true,false,true,true,false,true,false]
def lc (b : Bool) : Nat := if b then 24 else 16
def rc (b : Bool) : Nat := if b then 26 else 22
def width (b : Bool) : Int := if b then 14 else 10

def rep (w : List Bool) : Nat → List Bool
  | 0 => []
  | n+1 => w ++ rep w n

theorem rep_snoc (w : List Bool) (n : Nat) : rep w n ++ w = rep w (n+1) := by
  induction n with
  | zero => simp [rep]
  | succ n ih => simp only [rep, List.append_assoc, ih]

def rightEnc (b : Bool) : Nat → List Bool
  | 0 => [true]
  | n+1 => V b ++ (rep (U b) n ++ [true])

def peak (b : Bool) (n : Nat) (T : List Bool) (h : Int) : Z :=
  ⟨3,h,P ++ (rep (W b) n ++ T),[true]⟩

theorem left0 (b : Bool) (L R : List Bool) :
    zrun (table b) (lc b) ⟨3,0,P ++ (W b ++ L),R⟩ =
      some ⟨3,-width b,P ++ L,U b ++ R⟩ := by cases b <;> rfl

theorem leftOne (b : Bool) (h : Int) (L R : List Bool) :
    zrun (table b) (lc b) ⟨3,h,P ++ (W b ++ L),R⟩ =
      some ⟨3,h-width b,P ++ L,U b ++ R⟩ := by
  have H := zrun_shift (table b) h (lc b) ⟨3,0,P ++ (W b ++ L),R⟩
  rw [left0] at H
  simpa [shift, Int.sub_eq_add_neg, Int.add_comm] using H

theorem leftSweep (b : Bool) (n : Nat) (h : Int) (L R : List Bool) :
    zrun (table b) (lc b*n) ⟨3,h,P ++ (rep (W b) n ++ L),R⟩ =
      some ⟨3,h-width b*(n:Int),P ++ L,rep (U b) n ++ R⟩ := by
  induction n generalizing h R with
  | zero => simp [rep,zrun]
  | succ n ih =>
    have H := join (leftOne b h (rep (W b) n ++ L) R) (ih (h-width b) (U b ++ R))
    have he : lc b*(n+1)=lc b+lc b*n := by cases b <;> simp [lc] <;> omega
    have hh : h-width b-width b*(n:Int)=h-width b*((n+1:Nat):Int) := by cases b <;> simp [width] <;> omega
    rw [he]
    simpa only [rep,List.append_assoc,← List.append_assoc (rep (U b) n) (U b) R,rep_snoc,hh] using H

theorem right0 (b : Bool) (L R : List Bool) :
    zrun (table b) (rc b) ⟨3,0,S ++ L,V b ++ (U b ++ R)⟩ =
      some ⟨3,width b,S ++ (W b ++ L),V b ++ R⟩ := by cases b <;> rfl

theorem rightLast0 (b : Bool) (L : List Bool) :
    zrun (table b) (rc b) ⟨3,0,S ++ L,V b ++ [true]⟩ =
      some ⟨3,width b,S ++ (W b ++ L),[true]⟩ := by cases b <;> rfl

theorem rightOne (b : Bool) (n : Nat) (h : Int) (L : List Bool) :
    zrun (table b) (rc b) ⟨3,h,S ++ L,rightEnc b (n+1)⟩ =
      some ⟨3,h+width b,S ++ (W b ++ L),rightEnc b n⟩ := by
  cases n with
  | zero =>
    have H := zrun_shift (table b) h (rc b) ⟨3,0,S ++ L,V b ++ [true]⟩
    rw [rightLast0] at H
    simpa [shift,rightEnc,rep,Int.add_comm] using H
  | succ n =>
    have H := zrun_shift (table b) h (rc b) ⟨3,0,S ++ L,V b ++ (U b ++ (rep (U b) n ++ [true]))⟩
    rw [right0] at H
    simpa [shift,rightEnc,rep,List.append_assoc,Int.add_comm] using H

theorem rightSweep (b : Bool) (n : Nat) (h : Int) (L : List Bool) :
    zrun (table b) (rc b*n) ⟨3,h,S ++ L,rightEnc b n⟩ =
      some ⟨3,h+width b*(n:Int),S ++ (rep (W b) n ++ L),[true]⟩ := by
  induction n generalizing h L with
  | zero => simp [rep,zrun,rightEnc]
  | succ n ih =>
    have H := join (rightOne b n h L) (ih (h+width b) (W b ++ L))
    have he : rc b*(n+1)=rc b+rc b*n := by cases b <;> simp [rc] <;> omega
    have hh : h+width b+width b*(n:Int)=h+width b*((n+1:Nat):Int) := by cases b <;> simp [width] <;> omega
    rw [he]
    simpa only [rep,List.append_assoc,← List.append_assoc (rep (W b) n) (W b) L,rep_snoc,hh] using H

theorem finish0 (b : Bool) (L : List Bool) :
    zrun (table b) 6 ⟨3,0,S++L,[true]⟩ = some ⟨3,2,P++L,[true]⟩ := by cases b <;> rfl

theorem finish (b : Bool) (h : Int) (L : List Bool) :
    zrun (table b) 6 ⟨3,h,S++L,[true]⟩ = some ⟨3,h+2,P++L,[true]⟩ := by
  have H := zrun_shift (table b) h 6 ⟨3,0,S++L,[true]⟩
  rw [finish0] at H
  simpa [shift,Int.add_comm] using H

theorem turnFirst0 (b : Bool) (n : Nat) :
    zrun (table b) 31 ⟨3,0,P,rep (U b) n ++ [true]⟩ =
      some ⟨3,1,S++T1,rightEnc b n⟩ := by cases n <;> cases b <;> rfl

theorem turnFirst (b : Bool) (n : Nat) (h : Int) :
    zrun (table b) 31 ⟨3,h,P,rep (U b) n ++ [true]⟩ =
      some ⟨3,h+1,S++T1,rightEnc b n⟩ := by
  have H := zrun_shift (table b) h 31 ⟨3,0,P,rep (U b) n ++ [true]⟩
  rw [turnFirst0] at H
  simpa [shift,Int.add_comm] using H

theorem turnA0 (n : Nat) :
    zrun (table false) 31 ⟨3,0,P++T1,rep (U false) n ++ [true]⟩ =
      some ⟨3,-9,S,rightEnc false (n+1)⟩ := by rfl

theorem turnA (n : Nat) (h : Int) :
    zrun (table false) 31 ⟨3,h,P++T1,rep (U false) n ++ [true]⟩ =
      some ⟨3,h-9,S,rightEnc false (n+1)⟩ := by
  have H := zrun_shift (table false) h 31 ⟨3,0,P++T1,rep (U false) n ++ [true]⟩
  rw [turnA0] at H
  simpa [shift,Int.sub_eq_add_neg,Int.add_comm] using H

theorem turnB10 (n : Nat) :
    zrun (table true) 45 ⟨3,0,P++T1,rep (U true) n ++ [true]⟩ =
      some ⟨3,1,S++T2,rightEnc true n⟩ := by cases n <;> rfl

theorem turnB1 (n : Nat) (h : Int) :
    zrun (table true) 45 ⟨3,h,P++T1,rep (U true) n ++ [true]⟩ =
      some ⟨3,h+1,S++T2,rightEnc true n⟩ := by
  have H := zrun_shift (table true) h 45 ⟨3,0,P++T1,rep (U true) n ++ [true]⟩
  rw [turnB10] at H
  simpa [shift,Int.add_comm] using H

theorem turnB20 (n : Nat) :
    zrun (table true) 39 ⟨3,0,P++T2,rep (U true) n ++ [true]⟩ =
      some ⟨3,-13,S,rightEnc true (n+1)⟩ := by rfl

theorem turnB2 (n : Nat) (h : Int) :
    zrun (table true) 39 ⟨3,h,P++T2,rep (U true) n ++ [true]⟩ =
      some ⟨3,h-13,S,rightEnc true (n+1)⟩ := by
  have H := zrun_shift (table true) h 39 ⟨3,0,P++T2,rep (U true) n ++ [true]⟩
  rw [turnB20] at H
  simpa [shift,Int.sub_eq_add_neg,Int.add_comm] using H

theorem phase0 (b : Bool) (n : Nat) (h : Int) :
    zrun (table b) ((lc b + rc b)*n+37) (peak b n [] h) =
      some (peak b n T1 (h+3)) := by
  have H1 := leftSweep b n h [] [true]
  have H2 := turnFirst b n (h-width b*(n:Int))
  simp only [List.append_nil] at H1
  have H3 := rightSweep b n (h-width b*(n:Int)+1) T1
  have H4 := finish b (h-width b*(n:Int)+1+width b*(n:Int)) (rep (W b) n++T1)
  have H := join (join (join H1 H2) H3) H4
  have ht : lc b*n+31+rc b*n+6=(lc b+rc b)*n+37 := by cases b <;> simp [lc,rc] <;> omega
  have hh : h-width b*(n:Int)+1+width b*(n:Int)+2=h+3 := by omega
  simpa only [peak,List.append_nil,ht,hh] using H

theorem phaseA (n : Nat) (h : Int) :
    zrun (table false) (38*n+59) (peak false n T1 h) =
      some (peak false (n+1) [] (h+3)) := by
  have H1 := leftSweep false n h T1 [true]
  have H2 := turnA n (h-width false*(n:Int))
  have H3 := rightSweep false (n+1) (h-width false*(n:Int)-9) []
  simp only [List.append_nil] at H3
  have H4 := finish false (h-width false*(n:Int)-9+width false*((n+1:Nat):Int)) (rep (W false) (n+1))
  have H := join (join (join H1 H2) H3) H4
  have ht : lc false*n+31+rc false*(n+1)+6=38*n+59 := by simp [lc,rc]; omega
  have hh : h-width false*(n:Int)-9+width false*((n+1:Nat):Int)+2=h+3 := by simp [width]; omega
  simpa only [peak,List.append_nil,ht,hh] using H

theorem phaseB1 (n : Nat) (h : Int) :
    zrun (table true) (50*n+51) (peak true n T1 h) =
      some (peak true n T2 (h+3)) := by
  have H1 := leftSweep true n h T1 [true]
  have H2 := turnB1 n (h-width true*(n:Int))
  have H3 := rightSweep true n (h-width true*(n:Int)+1) T2
  have H4 := finish true (h-width true*(n:Int)+1+width true*(n:Int)) (rep (W true) n++T2)
  have H := join (join (join H1 H2) H3) H4
  have ht : lc true*n+45+rc true*n+6=50*n+51 := by simp [lc,rc]; omega
  have hh : h-width true*(n:Int)+1+width true*(n:Int)+2=h+3 := by omega
  simpa only [peak,List.append_nil,ht,hh] using H

theorem phaseB2 (n : Nat) (h : Int) :
    zrun (table true) (50*n+71) (peak true n T2 h) =
      some (peak true (n+1) [] (h+3)) := by
  have H1 := leftSweep true n h T2 [true]
  have H2 := turnB2 n (h-width true*(n:Int))
  have H3 := rightSweep true (n+1) (h-width true*(n:Int)-13) []
  simp only [List.append_nil] at H3
  have H4 := finish true (h-width true*(n:Int)-13+width true*((n+1:Nat):Int)) (rep (W true) (n+1))
  have H := join (join (join H1 H2) H3) H4
  have ht : lc true*n+39+rc true*(n+1)+6=50*n+71 := by simp [lc,rc]; omega
  have hh : h-width true*(n:Int)-13+width true*((n+1:Nat):Int)+2=h+3 := by simp [width]; omega
  simpa only [peak,List.append_nil,ht,hh] using H

theorem growthA (n : Nat) (h : Int) :
    zrun (table false) (76*n+96) (peak false n [] h) =
      some (peak false (n+1) [] (h+6)) := by
  have H := join (phase0 false n h) (phaseA n (h+3))
  have ht : (lc false+rc false)*n+37+(38*n+59)=76*n+96 := by simp [lc,rc]; omega
  have hh : h+3+3=h+6 := by omega
  simpa only [ht,hh] using H

theorem growthB (n : Nat) (h : Int) :
    zrun (table true) (150*n+159) (peak true n [] h) =
      some (peak true (n+1) [] (h+9)) := by
  have H := join (join (phase0 true n h) (phaseB1 n (h+3))) (phaseB2 n (h+3+3))
  have ht : (lc true+rc true)*n+37+(50*n+51)+(50*n+71)=150*n+159 := by simp [lc,rc]; omega
  have hh : h+3+3+3=h+9 := by omega
  simpa only [ht,hh] using H

def start : Z := ⟨0,0,[],[]⟩
theorem seed (b : Bool) : zrun (table b) 24 start = some (peak b 0 [] 4) := by cases b <;> rfl

def roundCost (b : Bool) (n : Nat) := if b then 150*n+159 else 76*n+96
def drift (b : Bool) : Int := if b then 9 else 6

theorem growth (b : Bool) (n : Nat) (h : Int) :
    zrun (table b) (roundCost b n) (peak b n [] h) =
      some (peak b (n+1) [] (h+drift b)) := by
  cases b with
  | false => exact growthA n h
  | true => exact growthB n h

theorem arbitraryRun (b : Bool) (N : Nat) :
    ∃ t n h, N ≤ t ∧ zrun (table b) t start = some (peak b n [] h) := by
  induction N with
  | zero => exact ⟨24,0,4,by omega,seed b⟩
  | succ N ih =>
    obtain ⟨t,n,h,ht,hr⟩ := ih
    exact ⟨t+roundCost b n,n+1,h+drift b,by cases b <;> simp [roundCost] <;> omega,join hr (growth b n h)⟩

theorem start_embed : embed start = blank := by
  unfold embed start blank
  congr 1
  funext x
  simp [atCell]

theorem never (b : Bool) (m : Machine) (hm : compatible (table b) m) : NeverHalts m := by
  intro N
  obtain ⟨t,n,h,ht,hr⟩ := arbitraryRun b N
  have H := zrun_sound (table b) m hm t _ _ hr
  rw [start_embed] at H
  rw [show t=N+(t-N) by omega,run_append] at H
  cases he : run m N blank with
  | none => simp [he] at H
  | some c => rfl

#print axioms growthA
#print axioms growthB
#print axioms seed
#print axioms arbitraryRun
#print axioms never
end BB6Coverage.Agent41Raw139ZeroLB
