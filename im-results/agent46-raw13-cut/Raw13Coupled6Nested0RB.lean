import SweepPumping
import FastFAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13Coupled6Nested0RB
open BB6Coverage BB6Coverage.Agent31Pump

-- Three literal partial tables, with identical macro behavior.
def p (d : Bool × Bool) : PartialMachine :=
  if d.1 then FAR.fromCodes [7,14,11,21,2,19,2,0,24,5,if d.2 then 12 else 8,5]
  else FAR.fromCodes [7,14,11,17,2,19,2,0,20,5,2,24]
abbrev U : List Bool := [true,true]
abbrev Z : List Bool := [false,false]
abbrev T : List Bool := [true,false]
abbrev Y : List Bool := [false,true]
abbrev A (l r : List Bool) : Z0 := ⟨0,l,r⟩
def rcfg (q : Fin 6) (l w : List Bool) : Z0 := ⟨q,w.headD false::l,w.tail⟩

def Reach (d : Bool × Bool) (a b : Z0) : Prop := ∃ n, run0 (p d) n a = some b

theorem reach_refl (d : Bool × Bool) (a : Z0) : Reach d a a := ⟨0,rfl⟩
theorem reach_join {d : Bool × Bool} {a b c : Z0} (h : Reach d a b) (g : Reach d b c) : Reach d a c := by
  obtain ⟨n,hn⟩ := h
  obtain ⟨m,hm⟩ := g
  exact ⟨n+m,join0 hn hm⟩

theorem bPair (d : Bool × Bool) (L W : List Bool) :
    run0 (p d) 2 (rcfg 1 L (U++W)) = some (rcfg 1 (Z++L) W) := by rcases d with ⟨d,e⟩; cases d <;> cases e <;> rfl

theorem bScan (d : Bool × Bool) (n : Nat) (L W : List Bool) :
    run0 (p d) (2*n) (rcfg 1 L (rep U n++W)) = some (rcfg 1 (rep Z n++L) W) := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have h := bPair d L (rep U n++W)
    have g := ih (Z++L)
    have H := join0 h g
    simpa only [rep,List.append_assoc,← List.append_assoc (rep Z n) Z L,rep_snoc Z n,show 2+2*n=2*(n+1) by omega] using H

theorem aPair (d : Bool × Bool) (L R : List Bool) :
    run0 (p d) 2 (A ([]++T++L) ([]++R)) = some (A ([]++L) ([]++U++R)) := by rcases d with ⟨d,e⟩; cases d <;> cases e <;> rfl

theorem aScan (d : Bool × Bool) (n : Nat) (L R : List Bool) :
    run0 (p d) (2*n) (A (rep T n++L) R) = some (A L (rep U n++R)) := by
  simpa only [List.nil_append] using sweepL (p d) 0 [] [] T U 2 (aPair d) n L R

theorem startB (d : Bool × Bool) (L W : List Bool) :
    run0 (p d) 1 (A (false::L) W) = some (rcfg 1 (true::L) W) := by rcases d with ⟨d,e⟩; cases d <;> cases e <;> rfl

theorem resetTail (d : Bool × Bool) (L : List Bool) :
    run0 (p d) 3 (rcfg 1 L [true,false]) = some (A L T) := by
  rcases d with ⟨d,e⟩; cases d <;> cases e <;> rfl

theorem reset (d : Bool × Bool) (j : Nat) (L : List Bool) :
    run0 (p d) (2*j+4) (A (false::L) (rep U j++T)) =
      some (A (rep Z j++true::L) T) := by
  have h := join0 (startB d L (rep U j++T)) (bScan d j (true::L) T)
  simpa only [show 1+2*j+3=2*j+4 by omega] using
    join0 h (resetTail d (rep Z j++true::L))

def encO : List Bool → List Bool
  | [] => []
  | b::bs => b::false::encO bs

theorem encO_append (a b : List Bool) : encO (a++b) = encO a++encO b := by
  induction a with
  | nil => rfl
  | cons a as ih => simp [encO,ih]

theorem encO_rep (b : Bool) (n : Nat) : encO (List.replicate n b) = rep [b,false] n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,encO,rep,ih]

theorem rep_add (P : List Bool) (a b : Nat) : rep P (a+b) = rep P a++rep P b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [Nat.succ_add,rep,ih,rep]; simp only [List.append_assoc]

theorem rep_right (P : List Bool) (n : Nat) : rep P (n+1) = rep P n++P := by
  rw [rep,rep_snoc]

theorem rotT (n : Nat) : [true]++rep Y n = rep T n++[true] := by simpa using rotate true [false] n
theorem rotZ (n : Nat) : [false]++rep Z n = rep Z n++[false] := by simpa using rotate false [false] n

def I (bits L : List Bool) : Z0 := A (encO bits++U++L) T

theorem innerInc (d : Bool × Bool) (j : Nat) (bits L : List Bool) :
    Reach d (I (List.replicate j true++false::bits) L) (I (List.replicate j false++true::bits) L) := by
  let W := encO bits++U++L
  have h := aScan d j (false::false::W) T
  have h' : run0 (p d) (2*j) (I (List.replicate j true++false::bits) L) =
      some (A (false::false::W) (rep U j++T)) := by
    simpa only [I,encO_append,encO_rep,encO,T,List.append_assoc,List.cons_append,List.nil_append,W] using h
  have g := reset d j (false::W)
  refine ⟨2*j+(2*j+4),?_⟩
  simpa only [I,encO_append,encO_rep,encO,Z,List.append_assoc,List.cons_append,List.nil_append,W] using join0 h' g

theorem replicate_right (j : Nat) (b : Bool) : List.replicate (j+1) b = List.replicate j b++[b] := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and]; exact ih

theorem innerFill (d : Bool × Bool) (j : Nat) (bits L : List Bool) :
    Reach d (I (List.replicate j false++bits) L) (I (List.replicate j true++bits) L) := by
  induction j generalizing bits with
  | zero => exact reach_refl d _
  | succ j ih =>
    have h := ih (false::bits)
    have g := innerInc d j bits L
    have f := ih (true::bits)
    simpa only [replicate_right j,List.append_assoc,List.singleton_append] using reach_join (reach_join h g) f

theorem innerFill2 (d : Bool × Bool) (j : Nat) (bits L : List Bool) :
    Reach d (I (false::true::(List.replicate j false++bits)) L)
      (I (List.replicate (j+2) true++bits) L) := by
  induction j generalizing bits with
  | zero => exact innerInc d 0 (true::bits) L
  | succ j ih =>
    have h := ih (false::bits)
    have g := innerInc d (j+2) bits L
    have f := innerFill d (j+2) (true::bits) L
    simpa only [replicate_right j,replicate_right (j+2),List.append_assoc,List.singleton_append] using reach_join (reach_join h g) f

theorem overflowTail (d : Bool × Bool) (L R : List Bool) :
    run0 (p d) 2 (A (U++L) R) = some (A L (Y++R)) := by
  rcases d with ⟨d,e⟩; cases d <;> cases e <;> rfl

theorem innerOverflow (d : Bool × Bool) (j : Nat) (L : List Bool) :
    run0 (p d) (2*j+2) (I (List.replicate j true) L) =
      some (A L ([false]++rep U (j+1)++[false])) := by
  have h := aScan d j (U++L) T
  have g := overflowTail d L (rep U j++T)
  have w : Y++(rep U j++T) = [false]++rep U (j+1)++[false] := by
    have rot1 : [true]++rep U j = rep U j++[true] := by simpa using rotate true [true] j
    change [false]++([true]++(rep U j++[true,false])) = _
    rw [← List.append_assoc [true] (rep U j),rot1,rep_right]
    simp only [U,List.append_assoc,List.cons_append,List.nil_append]
  simpa only [I,encO_rep,w,List.append_assoc] using join0 h g

theorem innerSetup (d : Bool × Bool) (m : Nat) (L : List Bool) :
    Reach d (A (T++rep Z (m+1)++U++L) [true])
      (I (false::true::List.replicate m false) L) := by
  have h := aScan d 1 (rep Z (m+1)++U++L) [true]
  have g := reset d 1 (false::(rep Z m++U++L))
  have g' : run0 (p d) 6 (A (false::false::(rep Z m++U++L)) [true,true,true]) =
      some (A (Z++T++rep Z m++U++L) T) := by
    have pad : run0 (p d) 6 (A (false::false::(rep Z m++U++L)) [true,true,true]) =
      run0 (p d) 6 (A (false::false::(rep Z m++U++L)) [true,true,true,false]) := by
      rcases d with ⟨d,e⟩; cases d <;> cases e <;> rfl
    rw [pad]
    simpa only [U,T,Z,rep,List.append_assoc,List.cons_append,List.nil_append] using g
  have h' : run0 (p d) 2 (A (T++rep Z (m+1)++U++L) [true]) =
      some (A (false::false::(rep Z m++U++L)) [true,true,true]) := by
    simpa only [rep,U,T,Z,List.append_assoc,List.cons_append,List.nil_append] using h
  refine ⟨8,?_⟩
  simpa only [I,encO,encO_rep,T,Z,List.append_assoc,List.cons_append,List.nil_append] using join0 h' g'

theorem innerFinish (d : Bool × Bool) (m : Nat) (L : List Bool) :
    Reach d (A (T++rep Z (m+1)++U++L) [true])
      (A L ([false]++rep U (m+3)++[false])) := by
  have h := innerSetup d m L
  have g := innerFill2 d m [] L
  simp only [List.append_nil] at g
  have f : Reach d (I (List.replicate (m+2) true) L)
      (A L ([false]++rep U (m+3)++[false])) := ⟨_,innerOverflow d (m+2) L⟩
  exact reach_join (reach_join h g) f

theorem marker (d : Bool × Bool) (L W : List Bool) :
    run0 (p d) 3 (rcfg 1 L (false::true::true::W)) =
      some (rcfg 1 (false::true::true::L) W) := by
  rcases d with ⟨d,e⟩; cases d <;> cases e <;> rfl

theorem endInit (d : Bool × Bool) (L : List Bool) :
    run0 (p d) 2 (rcfg 1 L [false]) =
      some (A (true::L) [true]) := by
  rcases d with ⟨d,e⟩; cases d <;> cases e <;> rfl

theorem init (d : Bool × Bool) (k m : Nat) (L : List Bool) :
    run0 (p d) (2*k+2*m+8)
      (A (false::L) (rep U k++([false]++rep U (m+2)++[false]))) =
      some (A (T++rep Z (m+1)++U++rep Z k++true::L) [true]) := by
  have h := join0 (startB d L (rep U k++([false]++rep U (m+2)++[false])))
      (bScan d k (true::L) ([false]++rep U (m+2)++[false]))
  have h' : run0 (p d) (1+2*k) (A (false::L) (rep U k++([false]++rep U (m+2)++[false]))) =
      some (rcfg 1 (rep Z k++true::L) (false::true::true::(rep U (m+1)++[false]))) := by
    simpa only [List.append_assoc,rep,U,List.cons_append,List.nil_append] using h
  have g := marker d (rep Z k++true::L) (rep U (m+1)++[false])
  have f := bScan d (m+1) (false::true::true::(rep Z k++true::L)) [false]
  have e := endInit d (rep Z (m+1)++false::true::true::(rep Z k++true::L))
  have H := join0 (join0 (join0 h' g) f) e
  have w : rep Z (m+1)++[false] = [false]++rep Z (m+1) := (rotZ (m+1)).symm
  have w' : true::(rep Z (m+1)++false::true::true::(rep Z k++true::L)) =
      T++rep Z (m+1)++U++rep Z k++true::L := by
    change [true]++(rep Z (m+1)++([false]++([true,true]++(rep Z k++true::L)))) = _
    rw [← List.append_assoc (rep Z (m+1)) [false],w]
    simp only [T,U,List.append_assoc,List.cons_append,List.nil_append]
  simpa only [w',show 1+2*k+3+2*(m+1)+2=2*k+2*m+8 by omega] using H

def O (bits : List Bool) (m : Nat) : Z0 := A (encO bits++[true]) ([false]++rep U (m+2)++[false])
def root (k m : Nat) : Z0 := A [] (rep U k++([false]++rep U (m+2)++[false]))

theorem outerInc (d : Bool × Bool) (j m : Nat) (bits : List Bool) :
    Reach d (O (List.replicate j true++false::bits) m)
      (O (List.replicate j false++true::bits) (m+1)) := by
  let L := false::(encO bits++[true])
  have h := aScan d j (false::L) ([false]++rep U (m+2)++[false])
  have h' : run0 (p d) (2*j) (O (List.replicate j true++false::bits) m) =
      some (A (false::L) (rep U j++([false]++rep U (m+2)++[false]))) := by
    simpa only [O,encO_append,encO_rep,encO,List.append_assoc,List.cons_append,L] using h
  have g := init d j m L
  obtain ⟨n,hn⟩ := innerFinish d m (rep Z j++true::L)
  have g' : run0 (p d) (2*j+2*m+8)
      (A (false::L) (rep U j++([false]++rep U (m+2)++[false]))) =
      some (A (T++rep Z (m+1)++U++(rep Z j++true::L)) [true]) := by
    simpa only [List.append_assoc] using g
  have H := join0 (join0 h' g') hn
  refine ⟨2*j+(2*j+2*m+8)+n,?_⟩
  simpa only [O,encO_append,encO_rep,encO,Z,List.append_assoc,List.cons_append,List.nil_append,L] using H

def count : Nat → Nat
  | 0 => 0
  | n+1 => count n+1+count n

theorem outerFill (d : Bool × Bool) (j m : Nat) (bits : List Bool) :
    Reach d (O (List.replicate j false++bits) m) (O (List.replicate j true++bits) (m+count j)) := by
  induction j generalizing m bits with
  | zero => exact reach_refl d _
  | succ j ih =>
    have h := ih m (false::bits)
    have g := outerInc d j (m+count j) bits
    have f := ih (m+count j+1) (true::bits)
    simpa only [replicate_right j,List.append_assoc,List.singleton_append,count,show m+count j+1+count j=m+(count j+1+count j) by omega] using reach_join (reach_join h g) f

theorem outerOverflow (d : Bool × Bool) (k m : Nat) :
    run0 (p d) (2*k+2) (O (List.replicate k true) m) = some (root (k+1) m) := by
  have h := aScan d k [true] ([false]++rep U (m+2)++[false])
  have g : run0 (p d) 2 (A [true] (rep U k++([false]++rep U (m+2)++[false]))) =
      some (root (k+1) m) := by
    rcases d with ⟨d,e⟩; cases d <;> cases e <;> rfl
  simpa only [O,encO_rep] using join0 h g

theorem rootGrowth (d : Bool × Bool) (k m : Nat) : ∃ n, 0 < n ∧
    run0 (p d) n (root k m) = some (root (k+1) (m+1+count k)) := by
  have h := init d k m []
  have h' : run0 (p d) (2*k+2*m+8) (root k m) =
      some (A (T++rep Z (m+1)++U++(encO (List.replicate k false)++[true])) [true]) := by
    have hu : ∀ n R, 0 < n → run0 (p d) n (A [] R) = run0 (p d) n (A [false] R) := by
      intro n R hN
      cases n with
      | zero => omega
      | succ n => rfl
    unfold root
    rw [hu _ _ (by omega)]
    simpa only [encO_rep,List.singleton_append,List.append_assoc] using h
  obtain ⟨n,hn⟩ := innerFinish d m (encO (List.replicate k false)++[true])
  have hn' : run0 (p d) n
      (A (T++rep Z (m+1)++U++(encO (List.replicate k false)++[true])) [true]) =
      some (O (List.replicate k false) (m+1)) := by exact hn
  obtain ⟨j,hj⟩ := outerFill d k (m+1) []
  simp only [List.append_nil] at hj
  have H := join0 (join0 (join0 h' hn') hj) (outerOverflow d k (m+1+count k))
  exact ⟨_,by omega,H⟩

def size : Nat → Nat
  | 0 => 2
  | n+1 => size n+1+count (n+2)

def family (k : Nat) : Z0 := root (k+2) (size k)

theorem seed (d : Bool × Bool) : run0 (p d) 107 (A [] []) = some (family 0) := by
  rcases d with ⟨d,e⟩; cases d <;> cases e <;> rfl

theorem familyGrowth (d : Bool × Bool) (k : Nat) : ∃ n, 0<n ∧ run0 (p d) n (family k) = some (family (k+1)) := by
  exact rootGrowth d (k+2) (size k)

theorem never (d : Bool × Bool) (m : Machine) (hm : compatible (p d) m) : NeverHalts m := by
  let cost := fun k => Classical.choose (familyGrowth d k)
  exact never_of_growth (p d) family 107 cost (seed d)
    (fun k => (Classical.choose_spec (familyGrowth d k)).1)
    (fun k => (Classical.choose_spec (familyGrowth d k)).2) m hm

#print axioms rootGrowth
#print axioms familyGrowth
#print axioms never
end BB6.Agent46Raw13Coupled6Nested0RB
