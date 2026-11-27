import SweepPumping
import FastFAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13Coupled6RDAlt
open BB6Coverage BB6Coverage.Agent31Pump

def p : PartialMachine := FAR.fromCodes [7,14,11,13,2,19,6,0,23,15,24,3]
abbrev Y : List Bool := [false,true]
abbrev U : List Bool := [true,true]
abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩

theorem rep_add (P : List Bool) (a b : Nat) : rep P (a+b) = rep P a ++ rep P b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [Nat.succ_add,rep,ih,rep]; simp only [List.append_assoc]

theorem rep_mul (P : List Bool) (a b : Nat) : rep (rep P a) b=rep P (a*b) := by
  induction b with
  | zero => rfl
  | succ b ih => rw [rep,ih,Nat.mul_succ,Nat.add_comm (a*b) a,rep_add]

theorem left (n : Nat) (L R : List Bool) :
    run0 p (2*n) (A (rep U n++L) R) = some (A L (rep Y n++R)) :=
  sweepL _ 0 [] [] U Y 2 (by intro L R; rfl) n L R

theorem start3 (L : List Bool) : run0 p 3 (A ([false]++L) [false]) = some (A (U++L) [true]) := by rfl

theorem unpad (n : Nat) (R : List Bool) (z : Z0) (h : 0 < n)
    (hr : run0 p n (A [false] R) = some z) : run0 p n (A [] R) = some z := by
  cases n with
  | zero => omega
  | succ n => exact hr

-- Transfer four alternating pairs to eight ones, keeping two right cells as lookahead.
theorem trans (n : Nat) (L R : List Bool) :
    run0 p (14*n) (A ([false]++L) (Y++rep Y (4*n)++R)) =
      some (A ([false]++rep U (4*n)++L) (Y++R)) := by
  have h := sweepR p 0 [false] Y (rep Y 4) (rep U 4) 14 (by intro L R; rfl) n L R
  simpa only [rep_mul] using h

theorem end3 (L : List Bool) : run0 p 7 (A ([false]++L) (Y++[true])) = some (A ([false,true,true,true]++L) [false]) := by rfl

theorem end5 (L : List Bool) : run0 p 5 (A ([false]++L) (rep Y 2++[true])) = some (A (rep U 3++L) []) := by rfl

theorem end8 (L : List Bool) : run0 p 14 (A ([false]++L) (rep Y 4)) = some (A ([false]++rep U 4++L) [false]) := by rfl

theorem padOdd (R : List Bool) : run0 p 8 (A [true] (rep Y 2++R)) = some (A [false,true,true] (rep Y 2++R)) := by rfl

def root (k : Nat) : Z0 := A ([false]++rep U (4*k+4)) [false]
def mid (k : Nat) : Z0 := A ([false]++rep U (4*k+5)++[true]) [false]

theorem evenPhase (k : Nat) : ∃ n, 0<n ∧ run0 p n (root k) = some (mid k) := by
  have h := start3 (rep U (4*k+4))
  have h' : run0 p 3 (root k) = some (A (rep U (4*k+5)++[]) [true]) := by
    simpa only [root,rep,List.append_nil] using h
  have g := join0 h' (left (4*k+5) [] [true])
  have ww : rep Y (4*k+5)++[true]=Y++rep Y (4*(k+1))++[true] := by
    rw [show 4*k+5=1+4*(k+1) by omega,rep_add]; rfl
  rw [ww] at g
  have ht := trans (k+1) [] [true]
  have ht' := unpad (14*(k+1)) _ _ (by omega) (by simpa only [List.append_nil] using ht)
  have q := join0 g ht'
  have hfin := end3 (rep U (4*(k+1)))
  have hfin' : run0 p 7 (A ([false]++rep U (4*(k+1))) (Y++[true])) = some (mid k) := by
    have w : [false,true,true,true]++rep U (4*(k+1))=[false]++rep U (4*k+5)++[true] := by
      have w1 : [true]++rep U (4*(k+1))=rep U (4*(k+1))++[true] := rotate true [true] _
      rw [show 4*k+5=4*(k+1)+1 by omega,rep]
      change [false]++U++([true]++rep U (4*(k+1))) = _
      rw [w1]; simp only [List.append_assoc]
    simpa only [mid,w] using hfin
  exact ⟨_,by omega,join0 q hfin'⟩

theorem oddPhase (k : Nat) : ∃ n, 0<n ∧ run0 p n (mid k) = some (root (k+1)) := by
  have h := start3 (rep U (4*k+5)++[true])
  have h' : run0 p 3 (mid k) = some (A (rep U (4*k+6)++[true]) [true]) := by
    simpa only [mid,rep,List.append_assoc] using h
  have g := join0 h' (left (4*k+6) [true] [true])
  have w : rep Y (4*k+6)++[true] = rep Y 2++(rep Y (4*(k+1))++[true]) := by
    rw [show 4*k+6=2+4*(k+1) by omega,rep_add]; simp only [List.append_assoc]
  rw [w] at g
  have q := join0 g (padOdd (rep Y (4*(k+1))++[true]))
  have ht := trans (k+1) U (Y++[true])
  have w1 : Y++rep Y (4*(k+1))++(Y++[true]) = rep Y 2++(rep Y (4*(k+1))++[true]) := by
    simp only [List.append_assoc]
    rw [show rep Y (4*(k+1))++(Y++[true])=Y++(rep Y (4*(k+1))++[true]) by rw [←List.append_assoc,rep_snoc]; simp only [List.append_assoc]]
    simp only [List.append_assoc,rep,List.append_nil]
  rw [w1] at ht
  have q' := join0 q ht
  have hf := end5 (rep U (4*(k+1))++U)
  have hff : run0 p 5 (A ([false]++rep U (4*(k+1))++U) (rep Y 2++[true])) = some (A (rep U (4*k+8)) []) := by
    rw [show 4*k+8=3+4*(k+1)+1 by omega,rep_add,rep_add]
    simpa only [List.append_assoc,rep,List.append_nil] using hf
  have r := join0 q' hff
  have l := left (4*k+8) [] []
  simp only [List.append_nil] at l
  have s := join0 r l
  have w2 : rep Y (4*k+8) = Y++rep Y (4*(k+1))++rep Y 3 := by
    rw [show 4*k+8=1+4*(k+1)+3 by omega,rep_add,rep_add]; rfl
  rw [w2] at s
  have ht2 := trans (k+1) [] (rep Y 3)
  have ht2' := unpad (14*(k+1)) _ _ (by omega) (by simpa only [List.append_nil] using ht2)
  have t := join0 s ht2'
  have he := end8 (rep U (4*(k+1)))
  have he' : run0 p 14 (A ([false]++rep U (4*(k+1))) (Y++rep Y 3)) = some (root (k+1)) := by
    rw [show Y++rep Y 3=rep Y 4 by rfl]
    have ww : rep U 4++rep U (4*(k+1)) = rep U (4*(k+1)+4) := by rw [Nat.add_comm _ 4,rep_add]
    simpa only [root,List.append_assoc,ww] using he
  exact ⟨_,by omega,join0 t he'⟩

theorem rootGrowth (k : Nat) : ∃ n, 0<n ∧ run0 p n (root k) = some (root (k+1)) := by
  obtain ⟨n,hn,h⟩ := evenPhase k
  obtain ⟨m,hm,g⟩ := oddPhase k
  exact ⟨n+m,by omega,join0 h g⟩

theorem seed : run0 p 54 (A [] []) = some (root 0) := by rfl

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
  let cost := fun k => Classical.choose (rootGrowth k)
  exact never_of_growth p root 54 cost seed
    (fun k => (Classical.choose_spec (rootGrowth k)).1)
    (fun k => (Classical.choose_spec (rootGrowth k)).2) m hm

#print axioms rootGrowth
#print axioms never
end BB6.Agent46Raw13Coupled6RDAlt
