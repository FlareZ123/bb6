import SweepPumping
import FastFAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13RCDouble
open BB6Coverage BB6Coverage.Agent31Pump
abbrev p : PartialMachine := FAR.fromCodes [7,14,11,6,2,19,22,0,7,9,24,10]
abbrev U : List Bool := [false,true,true,true,true,true]
abbrev I : List Bool := [false,true,false,true,true,true]
abbrev O : List Bool := [true,false,true,true,true,false]
abbrev J : List Bool := [false,true,false,true]
abbrev K : List Bool := [false,true,true,true]
abbrev T : List Bool := [false,true,true]
abbrev V : List Bool := [true,true,true,true,true,true]
abbrev S : List Bool := [true,true,true]
abbrev H : List Bool := [true,false,true,false]
abbrev R (n : Nat) := rep U n ++ T
abbrev A (l r : List Bool) : Z0 := ⟨0,l,r⟩
abbrev C (l r : List Bool) : Z0 := ⟨2,l,r⟩
def Reach (a b : Z0) : Prop := ∃ t, run0 p t a = some b
theorem reach {t : Nat} {a b : Z0} (h : run0 p t a = some b) : Reach a b := ⟨t,h⟩
theorem chain {a b c : Z0} (h : Reach a b) (g : Reach b c) : Reach a c := by
  obtain ⟨t,ht⟩ := h; obtain ⟨u,hu⟩ := g; exact ⟨t+u,join0 ht hu⟩
theorem rep_add' (B : List Bool) (n m : Nat) : rep B (n+m) = rep B n ++ rep B m := by
  induction n with
  | zero => simp [rep]
  | succ n ih => rw [Nat.succ_add,rep,ih]; simp [rep,List.append_assoc]
theorem initial (R : List Bool) : run0 p 6 (A [] (U++R)) = some (C (H++S) R) := by rfl
theorem initStep (L R : List Bool) :
  run0 p 12 (C (H++L) (U++R)) = some (C (H++O++L) R) := by rfl
theorem initEnd (L : List Bool) :
  run0 p 11 (C (H++L) T) = some (A (I++false::L) [true]) := by rfl
theorem rotateOI (n : Nat) : false :: rep O n = rep I n ++ [false] := by
  induction n with
  | zero => rfl
  | succ n ih => change I ++ (false :: rep O n) = I ++ (rep I n ++ [false]); rw [ih]
theorem initAll (n : Nat) : Reach (A [] (R (n+1))) (A (rep I (n+1)++K) [true]) := by
  have h1 := initial (R n)
  have h2 := sweepR p 2 H [] U O 12 (by intro L R; exact initStep L R) n S T
  have h3 := initEnd (rep O n++S)
  have h : Reach (A [] (R (n+1))) (A (I++false::(rep O n++S)) [true]) :=
    chain (chain (reach h1) (by simpa only [List.nil_append,List.append_assoc,R] using reach h2)) (reach h3)
  simpa only [← List.cons_append,rotateOI,rep,List.append_assoc,show [false]++S=K by rfl] using h

theorem takeStep (L R : List Bool) :
  run0 p 14 (A (J++L) (V++U++R)) = some (A (J++I++L) (V++R)) := by rfl
theorem takeEnd (L : List Bool) : run0 p 14 (A (J++L) (V++T)) = some (A (J++I++L) S) := by rfl
theorem close (L : List Bool) : run0 p 15 (A (J++L) S) = some (A (true::(I++L)) T) := by rfl
theorem unloadStep (L R : List Bool) :
  run0 p 6 (A (true::(I++L)) R) = some (A (true::L) (U++R)) := by rfl
theorem transfer (n : Nat) (L : List Bool) :
  Reach (A (J++L) (V++R n)) (A (true::L) (R (n+2))) := by
  have h1 := sweepR p 0 J V U I 14 (by intro L R; exact takeStep L R) n L T
  have h2 := takeEnd (rep I n++L)
  have h3 := close (I++rep I n++L)
  have h4 := sweepL p 0 [true] [] I U 6 (by intro L R; exact unloadStep L R) (n+2) L T
  have H : Reach (A (J++L) (V++R n)) (A (true::(rep I (n+2)++L)) T) := by
    simpa only [R,rep,List.append_assoc] using chain (chain (reach h1) (reach h2)) (reach h3)
  exact chain H (by simpa only [List.nil_append,List.singleton_append,List.cons_append,R] using reach h4)

theorem startPacket (L R : List Bool) : run0 p 18 (A (I++L) (J++U++R)) = some (A (J++U++L) (V++R)) := by rfl
theorem startSecond (L R : List Bool) : run0 p 8 (A (true::(U++L)) (U++R)) = some (A (J++S++L) (V++R)) := by rfl
theorem finishPacket (L R : List Bool) : run0 p 4 (A (true::S++L) R) = some (A L (J++R)) := by rfl
theorem packet (m : Nat) (L : List Bool) : Reach (A (I++L) (J++R (m+1))) (A L (J++R (m+3))) := by
  have h1 := startPacket L (R m)
  have h2 := transfer m (U++L)
  have h3 := startSecond L (R (m+1))
  have h4 := transfer (m+1) (S++L)
  have h5 := finishPacket L (R (m+3))
  exact chain (chain (chain (chain (reach h1) h2) (reach h3)) h4) (reach h5)
theorem firstPacket (L : List Bool) : run0 p 46 (A (I++L) [true]) = some (A L (J++R 1)) := by rfl

theorem packetSweep (n m : Nat) (L : List Bool) :
  Reach (A (rep I n++L) (J++R (m+1))) (A L (J++R (m+2*n+1))) := by
  induction n generalizing m with
  | zero => exact ⟨0,rfl⟩
  | succ n ih =>
    have h1 := packet m (rep I n++L)
    have h2 := ih (m+2)
    simpa only [rep,List.append_assoc,show m+2+1=m+3 by omega,show m+2+2*n+1=m+2*(n+1)+1 by omega] using chain h1 h2

theorem endStart (R : List Bool) : run0 p 22 (A K (J++U++R)) = some (A (J++[false,true,false,true,true]) (V++R)) := by rfl
theorem endFinish (R : List Bool) : run0 p 6 (A [true,false,true,false,true,true] R) = some (A [] (U++R)) := by rfl
theorem endPacket (m : Nat) : Reach (A K (J++R (m+1))) (A [] (R (m+3))) := by
  have h1 := endStart (R m)
  have h2 := transfer m [false,true,false,true,true]
  have h3 := endFinish (R (m+2))
  exact chain (chain (reach h1) h2) (reach h3)
theorem growth (n : Nat) : ∃ t, 0<t ∧ run0 p t (A [] (R (n+1))) = some (A [] (R (2*n+3))) := by
  obtain ⟨t,ht⟩ := initAll n
  have h1 := firstPacket (rep I n++K)
  have h2 := packetSweep n 0 K
  have h3 := endPacket (2*n)
  have h : Reach (A (rep I n++K) (J++R 1)) (A [] (R (2*n+3))) := by
    exact chain (by simpa only [Nat.zero_add] using h2) h3
  obtain ⟨u,hu⟩ := h
  exact ⟨t+46+u,by omega,join0 (join0 ht h1) hu⟩
def width : Nat → Nat
  | 0 => 0
  | n+1 => 2*width n+2
def family (n : Nat) : Z0 := A [] (R (width n+1))
theorem seed : run0 p 33 (A [] []) = some (family 0) := by rfl
theorem familyGrowth (n : Nat) : ∃ t, 0<t ∧ run0 p t (family n) = some (family (n+1)) := by
  simpa only [family,width,show ∀ k : Nat, 2*k+2+1=2*k+3 by intro k; omega] using growth (width n)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
  let cost := fun n => Classical.choose (familyGrowth n)
  exact never_of_growth p family 33 cost seed (fun n => (Classical.choose_spec (familyGrowth n)).1) (fun n => (Classical.choose_spec (familyGrowth n)).2) m hm
#print axioms growth
#print axioms never
end BB6.Agent46Raw13RCDouble
