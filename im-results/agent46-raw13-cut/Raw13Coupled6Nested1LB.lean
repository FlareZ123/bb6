import SweepPumping
import FastFAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13Coupled6Nested1LB
open BB6Coverage BB6Coverage.Agent31Pump

def p (d : Bool) : PartialMachine := FAR.fromCodes [7,14,11,21,2,19,2,0,24,6,if d then 12 else 8,5]
abbrev U : List Bool := [true,true]
abbrev Z : List Bool := [false,false]
abbrev T : List Bool := [true,false]
abbrev Y : List Bool := [false,true]
abbrev A (l r : List Bool) : Z0 := ⟨0,l,r⟩
def rcfg (q : Fin 6) (l w : List Bool) : Z0 := ⟨q,w.headD false::l,w.tail⟩

def Reach (d : Bool) (a b : Z0) : Prop := ∃ n, run0 (p d) n a = some b

theorem reach_refl (d : Bool) (a : Z0) : Reach d a a := ⟨0,rfl⟩
theorem reach_join {d : Bool} {a b c : Z0} (h : Reach d a b) (g : Reach d b c) : Reach d a c := by
  obtain ⟨n,hn⟩ := h
  obtain ⟨m,hm⟩ := g
  exact ⟨n+m,join0 hn hm⟩

theorem bPair (d : Bool) (L W : List Bool) :
    run0 (p d) 2 (rcfg 1 L (U++W)) = some (rcfg 1 (Z++L) W) := by cases d <;> rfl

theorem bScan (d : Bool) (n : Nat) (L W : List Bool) :
    run0 (p d) (2*n) (rcfg 1 L (rep U n++W)) = some (rcfg 1 (rep Z n++L) W) := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have h := bPair d L (rep U n++W)
    have g := ih (Z++L)
    have H := join0 h g
    simpa only [rep,List.append_assoc,← List.append_assoc (rep Z n) Z L,rep_snoc Z n,show 2+2*n=2*(n+1) by omega] using H

theorem aPair (d : Bool) (L R : List Bool) :
    run0 (p d) 2 (A ([]++T++L) ([]++R)) = some (A ([]++L) ([]++U++R)) := by cases d <;> rfl

theorem aScan (d : Bool) (n : Nat) (L R : List Bool) :
    run0 (p d) (2*n) (A (rep T n++L) R) = some (A L (rep U n++R)) := by
  simpa only [List.nil_append] using sweepL (p d) 0 [] [] T U 2 (aPair d) n L R

theorem startB (d : Bool) (L W : List Bool) :
    run0 (p d) 1 (A (false::L) W) = some (rcfg 1 (true::L) W) := by cases d <;> rfl

theorem resetTail (d : Bool) (L : List Bool) :
    run0 (p d) 3 (rcfg 1 L [true,false]) = some (A L T) := by cases d <;> rfl

theorem setOne (d : Bool) (L : List Bool) :
    run0 (p d) 4 (A (Z++L) T) = some (A (T++L) T) := by cases d <;> rfl

theorem reset (d : Bool) (s : Nat) (L : List Bool) :
    run0 (p d) (2*s+12) (A (false::L) (rep U (s+1)++[true,false])) =
      some (A (rep Z s++true::L) [true,true,true,false]) := by
  have h := join0 (startB d L (rep U (s+1)++[true,false])) (bScan d (s+1) (true::L) [true,false])
  have h2 := join0 h (resetTail d (rep Z (s+1)++true::L))
  have h3 := join0 h2 (setOne d (rep Z s++true::L))
  have h4 := join0 h3 (aPair d (rep Z s++true::L) T)
  simpa only [List.nil_append,show U++T=[true,true,true,false] by rfl,show 1+2*(s+1)+3+4+2=2*s+12 by omega] using h4

def encI : List Bool → List Bool
  | [] => []
  | b::bs => false::b::encI bs

def encO : List Bool → List Bool
  | [] => []
  | b::bs => b::false::encO bs

theorem encI_append (a b : List Bool) : encI (a++b) = encI a++encI b := by
  induction a with
  | nil => rfl
  | cons a as ih => simp [encI,ih]

theorem encO_append (a b : List Bool) : encO (a++b) = encO a++encO b := by
  induction a with
  | nil => rfl
  | cons a as ih => simp [encO,ih]

theorem encI_rep (b : Bool) (n : Nat) : encI (List.replicate n b) = rep [false,b] n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,encI,rep,ih]

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

def I (bits L : List Bool) : Z0 := A (false::(encI bits++true::L)) [true,true,true,false]

theorem innerInc (d : Bool) (j : Nat) (bits L : List Bool) :
    Reach d (I (List.replicate j true++false::bits) L) (I (List.replicate j false++true::bits) L) := by
  let W := encI bits++true::L
  have h1 := reset d 0 (encI (List.replicate j true++false::bits)++true::L)
  have h1' : run0 (p d) 12 (I (List.replicate j true++false::bits) L) =
      some (A (rep T (j+1)++false::W) [true,true,true,false]) := by
    have w : true::(encI (List.replicate j true++false::bits)++true::L) = rep T (j+1)++false::W := by
      rw [encI_append,encI_rep]
      simp only [encI,List.append_assoc,List.cons_append]
      change [true]++(rep Y j++(false::false::W)) = _
      rw [← List.append_assoc [true] (rep Y j),rotT,rep_right]
      simp only [List.append_assoc,T,List.cons_append,List.nil_append]
    simpa only [I,rep,List.nil_append,List.append_nil,w,show U++[true,false]=[true,true,true,false] by rfl] using h1
  have h2 := aScan d (j+1) (false::W) [true,true,true,false]
  have h2' : run0 (p d) (2*(j+1)) (A (rep T (j+1)++false::W) [true,true,true,false]) =
      some (A (false::W) (rep U (j+2)++[true,false])) := by
    have w : rep U (j+1)++[true,true,true,false] = rep U (j+2)++[true,false] := by
      rw [show rep U (j+2)=rep U (j+1)++U from rep_right U (j+1)]
      simp only [List.append_assoc,show U++[true,false]=[true,true,true,false] by rfl]
    simpa only [w] using h2
  have h3 := reset d (j+1) W
  have h3' : run0 (p d) (2*(j+1)+12) (A (false::W) (rep U (j+2)++[true,false])) =
      some (I (List.replicate j false++true::bits) L) := by
    have w : false::(encI (List.replicate j false++true::bits)++true::L) = rep Z (j+1)++true::W := by
      rw [encI_append,encI_rep]
      simp only [encI,List.append_assoc,List.cons_append]
      change [false]++(rep Z j++(false::true::W)) = _
      rw [← List.append_assoc [false] (rep Z j),rotZ,rep_right]
      simp only [List.append_assoc,Z,List.cons_append,List.nil_append]
    simpa only [I,w] using h3
  exact ⟨_,join0 (join0 h1' h2') h3'⟩

theorem replicate_right (j : Nat) (b : Bool) : List.replicate (j+1) b = List.replicate j b++[b] := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and]; exact ih

theorem innerFill (d : Bool) (j : Nat) (bits L : List Bool) :
    Reach d (I (List.replicate j false++bits) L) (I (List.replicate j true++bits) L) := by
  induction j generalizing bits with
  | zero => exact reach_refl d _
  | succ j ih =>
    have h := ih (false::bits)
    have g := innerInc d j bits L
    have f := ih (true::bits)
    simpa only [replicate_right j,List.append_assoc,List.singleton_append] using reach_join (reach_join h g) f

theorem overflowTail (d : Bool) (L R : List Bool) :
    run0 (p d) 2 (A ([true,true]++L) R) = some (A L ([false,true]++R)) := by cases d <;> rfl

theorem innerOverflow (d : Bool) (j : Nat) (L : List Bool) :
    run0 (p d) (14+2*j) (I (List.replicate j true) L) =
      some (A L ([false]++rep U (j+2)++[false])) := by
  have h := reset d 0 (encI (List.replicate j true)++true::L)
  have h' : run0 (p d) 12 (I (List.replicate j true) L) =
      some (A (rep T j++([true,true]++L)) [true,true,true,false]) := by
    have w : true::(encI (List.replicate j true)++true::L) = rep T j++([true,true]++L) := by
      rw [encI_rep]
      change [true]++(rep Y j++(true::L)) = _
      rw [← List.append_assoc [true] (rep Y j),rotT]
      simp only [List.append_assoc,List.cons_append,List.nil_append]
    simpa only [I,rep,List.nil_append,List.append_nil,w,show U++[true,false]=[true,true,true,false] by rfl] using h
  have h2 := aScan d j ([true,true]++L) [true,true,true,false]
  have h3 := overflowTail d L (rep U j++[true,true,true,false])
  have H := join0 (join0 h' h2) h3
  have w : [false,true]++(rep U j++[true,true,true,false]) = [false]++rep U (j+2)++[false] := by
    have rot1 : [true]++rep U j = rep U j++[true] := by simpa using rotate true [true] j
    change [false]++([true]++(rep U j++[true,true,true,false])) = _
    rw [← List.append_assoc [true] (rep U j),rot1]
    rw [show rep U (j+2)=rep U j++rep U 2 from rep_add U j 2]
    simp only [List.append_assoc,rep,U,List.cons_append,List.nil_append]
  simpa only [w,show 12+2*j+2=14+2*j by omega] using H

theorem padEq4 (d : Bool) (L : List Bool) :
    run0 (p d) 4 (A (false::L) [true,true,true]) =
      run0 (p d) 4 (A (false::L) [true,true,true,false]) := by cases d <;> rfl

theorem innerFinish (d : Bool) (j : Nat) (L : List Bool) :
    Reach d (A (false::(encI (List.replicate j false)++true::L)) [true,true,true])
      (A L ([false]++rep U (j+2)++[false])) := by
  obtain ⟨n,hn⟩ := innerFill d j [] L
  simp only [List.append_nil] at hn
  have h := join0 hn (innerOverflow d j L)
  have hN : n+(14+2*j)=4+(n+10+2*j) := by omega
  rw [hN,run0_add] at h
  refine ⟨4+(n+10+2*j),?_⟩
  rw [run0_add,padEq4]
  exact h

-- The marker handler enters E only with symbol one.
theorem marker (d : Bool) (L W : List Bool) :
    run0 (p d) 3 (rcfg 1 L (false::true::true::W)) =
      some (rcfg 1 (true::L) (true::true::W)) := by cases d <;> rfl

theorem endInit (d : Bool) (L : List Bool) :
    run0 (p d) 4 (rcfg 1 (Z++L) [false]) =
      some (A (false::L) [true,true,true]) := by cases d <;> rfl

-- Initialize the inner zero counter, preserving the outer-counter tail.
theorem init (d : Bool) (k m : Nat) (L : List Bool) :
    run0 (p d) (2*k+2*m+10)
      (A (false::L) (rep U k++([false]++rep U (m+1)++[false]))) =
      some (A (false::(encI (List.replicate m false)++true::(rep Z k++true::L))) [true,true,true]) := by
  have h := join0 (startB d L (rep U k++([false]++rep U (m+1)++[false])))
      (bScan d k (true::L) ([false]++rep U (m+1)++[false]))
  have h' : run0 (p d) (1+2*k) (A (false::L) (rep U k++([false]++rep U (m+1)++[false]))) =
      some (rcfg 1 (rep Z k++true::L) (false::true::true::(rep U m++[false]))) := by
    simpa only [List.append_assoc,rep,U,List.cons_append,List.nil_append] using h
  have g := marker d (rep Z k++true::L) (rep U m++[false])
  have f := bScan d (m+1) (true::(rep Z k++true::L)) [false]
  have hg := join0 h' g
  have hf := join0 hg f
  have hf' : run0 (p d) (1+2*k+3+2*(m+1))
      (A (false::L) (rep U k++([false]++rep U (m+1)++[false]))) =
      some (rcfg 1 (Z++(rep Z m++true::(rep Z k++true::L))) [false]) := by
    simpa only [rep,List.append_assoc] using hf
  have e := endInit d (rep Z m++true::(rep Z k++true::L))
  have H := join0 hf' e
  simpa only [encI_rep,List.append_assoc,show 1+2*k+3+2*(m+1)+4=2*k+2*m+10 by omega] using H

def O (bits : List Bool) (m : Nat) : Z0 := A (encO bits++[true]) ([false]++rep U (m+1)++[false])
def root (k m : Nat) : Z0 := A [] (rep U k++([false]++rep U (m+1)++[false]))

theorem outerInc (d : Bool) (j m : Nat) (bits : List Bool) :
    Reach d (O (List.replicate j true++false::bits) m)
      (O (List.replicate j false++true::bits) (m+1)) := by
  let L := false::(encO bits++[true])
  have h := aScan d j (false::L) ([false]++rep U (m+1)++[false])
  have h' : run0 (p d) (2*j) (O (List.replicate j true++false::bits) m) =
      some (A (false::L) (rep U j++([false]++rep U (m+1)++[false]))) := by
    simpa only [O,encO_append,encO_rep,encO,List.append_assoc,List.cons_append,L] using h
  have g := init d j m L
  have f := innerFinish d m (rep Z j++true::L)
  obtain ⟨n,hn⟩ := f
  have H := join0 (join0 h' g) hn
  refine ⟨2*j+(2*j+2*m+10)+n,?_⟩
  simpa only [O,encO_append,encO_rep,encO,List.append_assoc,List.cons_append,L] using H

def count : Nat → Nat
  | 0 => 0
  | n+1 => count n+1+count n

theorem outerFill (d : Bool) (j m : Nat) (bits : List Bool) :
    Reach d (O (List.replicate j false++bits) m) (O (List.replicate j true++bits) (m+count j)) := by
  induction j generalizing m bits with
  | zero => exact reach_refl d _
  | succ j ih =>
    have h := ih m (false::bits)
    have g := outerInc d j (m+count j) bits
    have f := ih (m+count j+1) (true::bits)
    simpa only [replicate_right j,List.append_assoc,List.singleton_append,count,show m+count j+1+count j=m+(count j+1+count j) by omega] using reach_join (reach_join h g) f

theorem outerOverflow (d : Bool) (k m : Nat) :
    run0 (p d) (2*k+2) (O (List.replicate k true) m) = some (root (k+1) m) := by
  have h := aScan d k [true] ([false]++rep U (m+1)++[false])
  have g : run0 (p d) 2 (A [true] (rep U k++([false]++rep U (m+1)++[false]))) =
      some (root (k+1) m) := by
    cases d <;> rfl
  simpa only [O,encO_rep] using join0 h g

theorem rootGrowth (d : Bool) (k m : Nat) : ∃ n, 0 < n ∧
    run0 (p d) n (root k m) = some (root (k+1) (m+1+count k)) := by
  have h := init d k m []
  have h' : run0 (p d) (2*k+2*m+10) (root k m) =
      some (A (false::(encI (List.replicate m false)++true::(encO (List.replicate k false)++[true]))) [true,true,true]) := by
    have hu : ∀ n R, 0 < n → run0 (p d) n (A [] R) = run0 (p d) n (A [false] R) := by
      intro n R hN
      cases n with
      | zero => omega
      | succ n => rfl
    unfold root
    rw [hu _ _ (by omega)]
    simpa only [encO_rep,List.singleton_append] using h
  obtain ⟨n,hn⟩ := innerFinish d m (encO (List.replicate k false)++[true])
  have hn' : run0 (p d) n
      (A (false::(encI (List.replicate m false)++true::(encO (List.replicate k false)++[true]))) [true,true,true]) =
      some (O (List.replicate k false) (m+1)) := by exact hn
  obtain ⟨j,hj⟩ := outerFill d k (m+1) []
  simp only [List.append_nil] at hj
  have H := join0 (join0 (join0 h' hn') hj) (outerOverflow d k (m+1+count k))
  exact ⟨_,by omega,H⟩

def size : Nat → Nat
  | 0 => 1
  | n+1 => size n+1+count (n+1)

def family (k : Nat) : Z0 := root (k+1) (size k)

theorem seed (d : Bool) : run0 (p d) 31 (A [] []) = some (family 0) := by cases d <;> rfl

theorem familyGrowth (d : Bool) (k : Nat) : ∃ n, 0<n ∧ run0 (p d) n (family k) = some (family (k+1)) := by
  exact rootGrowth d (k+1) (size k)

-- Existential positive-step witnesses avoid evaluating the enormous times.
theorem never (d : Bool) (m : Machine) (hm : compatible (p d) m) : NeverHalts m := by
  let cost := fun k => Classical.choose (familyGrowth d k)
  exact never_of_growth (p d) family 31 cost (seed d)
    (fun k => (Classical.choose_spec (familyGrowth d k)).1)
    (fun k => (Classical.choose_spec (familyGrowth d k)).2) m hm

#print axioms rootGrowth
#print axioms familyGrowth
#print axioms never
end BB6.Agent46Raw13Coupled6Nested1LB
