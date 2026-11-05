import Lean.Elab.Tactic.Omega
import CryptidTriplePairs
import EGenericTurn

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

namespace BB6.Agent2ATurnFamily
open CryptidBoundary

def front (r : Nat) : List Bool :=
  [true,true] ++ (oppairs r ++ [true,true])

def aStart (r : Nat) (L ys : List Bool) : Cfg :=
  ⟨L,false,front r ++ ys,0⟩

def aScan (i r : Nat) (L ys : List Bool) : Cfg :=
  ⟨oppairs i ++ (true::L),false,
    true :: (oppairs r ++ ([true,true] ++ ys)),0⟩

private theorem aStart_five (r : Nat) (L ys : List Bool) :
    run 5 (aStart (r+1) L ys) = aScan 0 (r+1) L ys := by
  simp [aStart,front,aScan,run,step,goL,goR,oppairs,List.append_assoc]

private theorem aScan_two (i r : Nat) (L ys : List Bool) :
    run 2 (aScan i (r+1) L ys) =
      aScan (i+1) r L ys := by
  simp [aScan,run,step,goL,goR,oppairs,List.append_assoc]

private theorem aScan_run (i r : Nat) (L ys : List Bool) :
    run (2*r) (aScan i r L ys) = aScan (r+i) 0 L ys := by
  induction r generalizing i with
  | zero => simp [run]
  | succ r ih =>
      have ht : 2*(r+1) = 2+2*r := by omega
      rw [ht,run_add,aScan_two,ih (i+1)]
      have heq : r+(i+1) = (r+1)+i := by omega
      rw [heq]

private theorem alternating (n : Nat) (ys : List Bool) :
    true :: (oppairs n ++ ([false,true,false] ++ ys)) =
    pairs (n+2) ++ ys := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [oppairs, pairs, List.cons_append]
      simpa [pairs] using congrArg (fun z : List Bool => true::false::z) ih

/-- Literal six-state A turn for EVERY positive r and arbitrary unknown
    left tape and right suffix; it is an unbounded source-inductive result. -/
theorem a_turn_all (r : Nat) (L ys : List Bool) :
    run (6*(r+1)+14) (aStart (r+1) L ys) =
      ⟨L,true,pairs (r+3) ++ ys,2⟩ := by
  let n := r+1
  have ht : 6*(r+1)+14 = 5+(2*n+(8+(4*n+1))) := by
    dsimp [n]
    omega
  rw [ht,run_add,aStart_five]
  rw [run_add,aScan_run]
  rw [run_add]
  change run (4*n+1)
    (run 8 (⟨oppairs n ++ (true::L),false,[true,true,true] ++ ys,0⟩ : Cfg)) = _
  rw [aTriple8]
  rw [run_add]
  change run 1
    (run (4*n) (bPop n (true::L) ([false,true,false] ++ ys))) = _
  rw [bPop_run]
  change run 1
    (⟨true::L,false,oppairs n ++ ([false,true,false] ++ ys),1⟩ : Cfg) = _
  simp only [run,step,goL,goR]
  simpa [n] using alternating (r+1) ys

/-- Every positive alternating 01-stack between the two 11 termini
    gives a parameter-unbounded original-source E return. -/
theorem full_E_alternating_family (k q r : Nat) (ys : List Bool) :
    run (12*k*k+49*k+6*(r+1)+62+4*q)
      (init (List.replicate (3*k+2) true ++
        false :: (pairs q ++ (front (r+1) ++ ys)))) =
      ⟨[],false,List.replicate (8*k+3) true ++
        BB6.Agent2EGenericTurn.outPacket q (pairs (r+3)) ys,5⟩ := by
  have ht : 12*k*k+49*k+6*(r+1)+62+4*q =
    12*k*k+49*k+(6*(r+1)+14)+48+4*q := by omega
  rw [ht]
  apply BB6.Agent2EGenericTurn.full_E_from_turn
  intro L
  simpa [aStart] using a_turn_all r L ys


/-- No state-F visit in the first n primitive transitions. Since a return
    requires state F, this implies absence of physical first returns. -/
def NoF (c : Cfg) (n : Nat) : Prop :=
  ∀ t, t<n → (run t c).st ≠ 5

private theorem appendNoF (c d : Cfg) (a b : Nat)
    (hc : NoF c a) (he : run a c = d) (hd : NoF d b) :
    NoF c (a+b) := by
  intro t ht
  by_cases hshort : t<a
  · exact hc t hshort
  · have heq : t=a+(t-a) := by omega
    rw [heq,run_add,he]
    exact hd (t-a) (by omega)

private theorem aStart_five_noF (r : Nat) (L ys : List Bool) :
    NoF (aStart (r+1) L ys) 5 := by
  intro t ht
  have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl
  all_goals simp [aStart,front,oppairs,run,step,goL,goR]

private theorem aScan_two_noF (i r : Nat) (L ys : List Bool) :
    NoF (aScan i (r+1) L ys) 2 := by
  intro t ht
  have cases : t=0 ∨ t=1 := by omega
  rcases cases with rfl | rfl
  all_goals simp [aScan,run,step,goL,goR,oppairs]

private theorem aScan_run_noF (i r : Nat) (L ys : List Bool) :
    NoF (aScan i r L ys) (2*r) := by
  induction r generalizing i with
  | zero =>
      intro t ht
      omega
  | succ r ih =>
      have htime : 2*(r+1)=2+2*r := by omega
      rw [htime]
      exact appendNoF
        (aScan i (r+1) L ys) (aScan (i+1) r L ys)
        2 (2*r)
        (aScan_two_noF i r L ys)
        (aScan_two i r L ys) (ih (i+1))

private theorem tripleEight_noF (L ys : List Bool) :
    NoF (⟨L,false,[true,true,true]++ys,0⟩ : Cfg) 8 := by
  intro t ht
  have cases :
      t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ t=7 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    cases L with
    | nil => simp [run,step,goL,goR]
    | cons v L => cases v <;> simp [run,step,goL,goR]

private theorem bPop_four_noF (n : Nat) (L ys : List Bool) :
    NoF (bPop (n+1) L ys) 4 := by
  intro t ht
  have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  all_goals simp [bPop,oppairs,run,step,goL,goR]

private theorem bPop_run_noF (n : Nat) (L ys : List Bool) :
    NoF (bPop n L ys) (4*n) := by
  induction n generalizing ys with
  | zero =>
      intro t ht
      omega
  | succ n ih =>
      have htime : 4*(n+1)=4+4*n := by omega
      rw [htime]
      exact appendNoF
        (bPop (n+1) L ys) (bPop n L (false::true::ys))
        4 (4*n)
        (bPop_four_noF n L ys)
        (bPop_step n L ys) (ih (false::true::ys))

/-- The unbounded A/0 alternating-tail source turn never visits F, for
    every unknown left tape and every unknown right suffix. -/
theorem a_turn_all_noF (r : Nat) (L ys : List Bool) :
    NoF (aStart (r+1) L ys) (6*(r+1)+14) := by
  let n := r+1
  have ht : 6*(r+1)+14=5+(2*n+(8+(4*n+1))) := by
    dsimp [n]
    omega
  rw [ht]
  have hs : run 5 (aStart (r+1) L ys) = aScan 0 n L ys := by
    simpa only [n] using aStart_five r L ys
  apply appendNoF (aStart (r+1) L ys)
    (aScan 0 n L ys) 5 (2*n+(8+(4*n+1)))
    (aStart_five_noF r L ys) hs
  have hscan : run (2*n) (aScan 0 n L ys) =
      (⟨oppairs n++(true::L),false,[true,true,true]++ys,0⟩ : Cfg) := by
    rw [aScan_run]
    rfl
  apply appendNoF (aScan 0 n L ys)
    (⟨oppairs n++(true::L),false,[true,true,true]++ys,0⟩ : Cfg)
    (2*n) (8+(4*n+1))
    (aScan_run_noF 0 n L ys) hscan
  let a : Cfg := ⟨oppairs n++(true::L),false,[true,true,true]++ys,0⟩
  let b : Cfg := bPop n (true::L) ([false,true,false]++ys)
  have h8 : run 8 a = b := by
    dsimp [a,b]
    exact aTriple8 (oppairs n++(true::L)) ys
  apply appendNoF a b 8 (4*n+1)
    (tripleEight_noF (oppairs n++(true::L)) ys) h8
  have hpop : run (4*n) b =
      (⟨true::L,false,oppairs n++([false,true,false]++ys),1⟩ : Cfg) := by
    dsimp [b]
    rw [bPop_run]
  apply appendNoF b
    (⟨true::L,false,oppairs n++([false,true,false]++ys),1⟩ : Cfg)
    (4*n) 1
    (bPop_run_noF n (true::L) ([false,true,false]++ys))
    hpop
  intro t hlt
  have hzero : t=0 := by omega
  subst t
  simp [run]

#print axioms a_turn_all_noF
#print axioms aStart_five
#print axioms aScan_two
#print axioms aScan_run
#print axioms a_turn_all
#print axioms full_E_alternating_family
end BB6.Agent2ATurnFamily
