import Lean.Elab.Tactic.Omega
import E111FirstReturn

namespace BB6.CryptidPrefixFirstReturn
open CryptidBoundary
open BB6.Agent2EOneTriple
open BB6.CryptidE111FirstReturn

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def NoF (c : Cfg) (n : Nat) : Prop :=
  ∀ t, t < n → (run t c).st ≠ 5

private theorem appendNoF (c d : Cfg) (a b : Nat)
    (hc : NoF c a) (he : run a c = d) (hd : NoF d b) :
    NoF c (a+b) := by
  intro t ht
  by_cases hsmall : t < a
  · exact hc t hsmall
  · obtain ⟨u, hu⟩ : ∃ u, t = a+u := ⟨t-a,by omega⟩
    rw [hu,run_add,he]
    exact hd (t-a) (by omega)

private theorem frontNoF (m : Nat) (L ys : List Bool) :
    NoF (front m L ys) (2*m+3) := by
  induction m generalizing L ys with
  | zero =>
    intro t ht
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with rfl | rfl | rfl
    all_goals simp [front,run,step,goL,goR,pairs]
  | succ m ih =>
    intro t ht
    by_cases hsmall : t < 2
    · have hcases : t=0 ∨ t=1 := by omega
      rcases hcases with rfl | rfl
      all_goals simp [front,run,step,goL,goR,pairs]
    · obtain ⟨u, hu⟩ : ∃ u, t=2+u := ⟨t-2,by omega⟩
      rw [hu,run_add,front_step]
      exact ih ([false,true]++L) ys (t-2) (by omega)

private theorem reverseNoF (m : Nat) (ys : List Bool) :
    NoF (revTurn m ys) (4*m+24) := by
  induction m generalizing ys with
  | zero =>
    intro t ht
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ t=7 ∨ t=8 ∨ t=9 ∨ t=10 ∨ t=11 ∨ t=12 ∨ t=13 ∨ t=14 ∨ t=15 ∨ t=16 ∨ t=17 ∨ t=18 ∨ t=19 ∨ t=20 ∨ t=21 ∨ t=22 ∨ t=23 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [revTurn,run,step,goL,goR,pairs]
  | succ m ih =>
    intro t ht
    by_cases hsmall : t < 4
    · have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
      rcases hcases with rfl | rfl | rfl | rfl
      all_goals simp [revTurn,run,step,goL,goR,pairs]
    · obtain ⟨u, hu⟩ : ∃ u, t=4+u := ⟨t-4,by omega⟩
      rw [hu,run_add,reverse_step]
      exact ih ([true,false]++ys) (t-4) (by omega)

private theorem scanNoF (m : Nat) (L ys : List Bool) :
    NoF (scanStart m L ys) (2*m) := by
  induction m generalizing L ys with
  | zero =>
    intro t ht
    omega
  | succ m ih =>
    intro t ht
    by_cases hsmall : t<2
    · have hcases : t=0 ∨ t=1 := by omega
      rcases hcases with rfl | rfl
      all_goals simp [scanStart,run,step,goL,goR,pairs]
    · obtain ⟨u, hu⟩ : ∃ u, t=2+u := ⟨t-2,by omega⟩
      rw [hu,run_add,scan_step]
      exact ih ([false,true]++L) ys (t-2) (by omega)

private theorem boundaryENoF (m : Nat) (ys : List Bool) :
    NoF (midM m ([true,true,false]++ys)) (2*m+3) := by
  have hscan : NoF (scanStart m [true] ([true,true,false]++ys)) (2*m) :=
    scanNoF m [true] ([true,true,false]++ys)
  have hend : NoF (scanDone m [true] ([true,true,false]++ys)) 3 := by
    intro t ht
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with rfl | rfl | rfl
    all_goals simp [scanDone,run,step,goL,goR]
  exact appendNoF
    (scanStart m [true] ([true,true,false]++ys))
    (scanDone m [true] ([true,true,false]++ys))
    (2*m) 3 hscan (scan_run m [true] ([true,true,false]++ys)) hend

private theorem pumpNoF (m : Nat) (ys : List Bool) :
    NoF (midM m ([true,true,true]++ys)) (6*m+27) := by
  have hf : NoF (front m [true] ys) (2*m+3) := frontNoF m [true] ys
  have hr : NoF (revTurn m ys) (4*m+24) := reverseNoF m ys
  have he : run (2*m+3) (front m [true] ys) = revTurn m ys := by
    rw [front_run]
    simp [turn,revTurn,List.append_assoc]
  have h := appendNoF
    (front m [true] ys) (revTurn m ys) (2*m+3) (4*m+24) hf he hr
  have h0 : NoF (front m [true] ys) (6*m+27) := by
    simpa only [show (2*m+3)+(4*m+24)=6*m+27 by omega] using h
  simpa [midM,front,List.append_assoc] using h0

private theorem pumpIterNoF (k : Nat) (ys : List Bool) :
    NoF (midM 3 (List.replicate (3*k) true ++ ys)) (pumpTime k) := by
  induction k generalizing ys with
  | zero =>
    intro t ht
    simp [pumpTime] at ht
  | succ k ih =>
    have hrep : List.replicate (3*(k+1)) true ++ ys =
      List.replicate (3*k) true ++ ([true,true,true] ++ ys) := by
      rw [show 3*(k+1)=3*k+3 by omega, ←List.replicate_append_replicate]
      simp only [List.replicate_succ, List.replicate_zero,
        List.append_nil,List.append_assoc]
    change NoF (midM 3 (List.replicate (3*(k+1)) true ++ys))
      (pumpTime k+(6*(4*k+3)+27))
    rw [hrep]
    exact appendNoF
      (midM 3 (List.replicate (3*k) true ++ ([true,true,true]++ys)))
      (midM (4*k+3) ([true,true,true]++ys))
      (pumpTime k) (6*(4*k+3)+27)
      (ih ([true,true,true]++ys))
      (pump_iter k ([true,true,true]++ys))
      (pumpNoF (4*k+3) ys)

private theorem setupPositiveNoF (xs : List Bool) (t : Nat)
    (ht0 : 0<t) (ht : t<24) :
    (run t (init xs)).st ≠ 5 := by
  have hcases : t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ t=7 ∨ t=8 ∨ t=9 ∨ t=10 ∨ t=11 ∨ t=12 ∨ t=13 ∨ t=14 ∨ t=15 ∨ t=16 ∨ t=17 ∨ t=18 ∨ t=19 ∨ t=20 ∨ t=21 ∨ t=22 ∨ t=23 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [init,run,step,goL,goR]

/-- The exact first-delimiter F-to-E prefix has no state F anywhere after
    its initial time zero. The tape suffix is fully arbitrary. -/
theorem prefixE_positive_noF (k : Nat) (ys : List Bool) (t : Nat)
    (hpos : 0<t) (ht : t<12*k*k+41*k+33) :
    (run t (init (List.replicate (3*k+2) true ++ false::ys))).st ≠ 5 := by
  have hrep : List.replicate (3*k+2) true ++ false::ys =
      List.replicate (3*k) true ++ ([true,true,false]++ys) := by
    rw [show 3*k+2=3*k+1+1 by omega]
    simp [List.replicate_succ,List.append_assoc]
  have htime : 12*k*k+41*k+33 =
      24+pumpTime k+(2*(4*k+3)+3) := by
    rw [pumpTime_formula]
    omega
  rw [htime] at ht
  by_cases hfirst : t<24
  · exact setupPositiveNoF _ t hpos hfirst
  · obtain ⟨u,hu⟩ : ∃ u, t=24+u := ⟨t-24,by omega⟩
    rw [hu,run_add]
    have hs : run 24 (init (List.replicate (3*k+2) true ++false::ys)) =
        midM 3 (List.replicate (3*k) true ++ ([true,true,false]++ys)) := by
      rw [hrep]
      simpa [mid,midM] using
        (setup24 (List.replicate (3*k) true ++ ([true,true,false]++ys)))
    rw [hs]
    by_cases hpump : u<pumpTime k
    · exact pumpIterNoF k ([true,true,false]++ys) u hpump
    · have hu' : u=pumpTime k+(u-pumpTime k) := by omega
      rw [hu',run_add,pump_iter]
      exact boundaryENoF (4*k+3) ys (u-pumpTime k) (by omega)

#print axioms frontNoF
#print axioms reverseNoF
#print axioms scanNoF
#print axioms boundaryENoF
#print axioms pumpNoF
#print axioms pumpIterNoF
#print axioms prefixE_positive_noF

end BB6.CryptidPrefixFirstReturn
