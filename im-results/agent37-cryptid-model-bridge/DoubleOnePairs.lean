import Lean.Elab.Tactic.Omega
import DoubleOneBranch
import A1100First

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

namespace BB6.CryptidBridge
open CryptidBoundary

private def qB : Nat → List Bool → List Bool → Cfg
  | 0,L,ys => ⟨L,false,ys,1⟩
  | q+1,L,ys => ⟨L,true,false::(pairs q ++ (false::ys)),1⟩

private def qFrontL (n : Nat) : List Bool :=
  [true,false,true,true,false] ++ pairs n ++ [true,true]

private def qCoreL (m : Nat) : List Bool :=
  [true,true,false] ++ pairs (m+2) ++ [true,true]

private theorem q_pairs_snoc (q : Nat) :
    pairs q ++ [true,false] = pairs (q+1) := by
  induction q with
  | zero => rfl
  | succ q ih => simp [pairs,ih,List.append_assoc]

private theorem q_b_two (q : Nat) (L ys : List Bool) :
    run 2 (qB (q+1) L ys) = qB q ([true,false] ++ L) ys := by
  cases q with
  | zero => simp [qB,run,step,goL,goR,pairs]
  | succ q => simp [qB,run,step,goL,goR,pairs]

private theorem q_b_scan (q : Nat) (L ys : List Bool) :
    run (2*q) (qB q L ys) = ⟨pairs q ++ L,false,ys,1⟩ := by
  induction q generalizing L with
  | zero => rfl
  | succ q ih =>
    have ht : 2*(q+1) = 2+(2*q) := by omega
    rw [ht,run_add,q_b_two,ih]
    congr 1
    calc
      pairs q ++ (true :: false :: L) =
          (pairs q ++ [true,false]) ++ L := by simp [List.append_assoc]
      _ = pairs (q+1) ++ L := by rw [q_pairs_snoc]

private theorem q_d_two (q : Nat) (L ys : List Bool) :
    run 2 ⟨pairs (q+1) ++ L,false,ys,3⟩ =
      ⟨pairs q ++ L,false,[true,true] ++ ys,3⟩ := by
  simp [run,step,goL,goR,pairs]

private theorem q_d_scan (q : Nat) (L ys : List Bool) :
    run (2*q) ⟨pairs q ++ L,false,ys,3⟩ =
      ⟨L,false,List.replicate (2*q) true ++ ys,3⟩ := by
  induction q generalizing ys with
  | zero => rfl
  | succ q ih =>
    have ht : 2*(q+1) = 2+(2*q) := by omega
    rw [ht,run_add,q_d_two,ih]
    congr 1
    have hrep : List.replicate (2*q) true ++ [true,true] =
        List.replicate (2+2*q) true := by
      calc
        List.replicate (2*q) true ++ [true,true] =
            List.replicate (2*q) true ++ List.replicate 2 true := rfl
        _ = List.replicate ((2*q)+2) true := List.replicate_append_replicate
        _ = List.replicate (2+2*q) true := by congr 1
    calc
      List.replicate (2*q) true ++ ([true,true] ++ ys) =
          (List.replicate (2*q) true ++ [true,true]) ++ ys := by simp [List.append_assoc]
      _ = List.replicate (2+2*q) true ++ ys := by rw [hrep]

private theorem q_front8 (n q : Nat) (ys : List Bool) :
    run 8 (preA n ([true,true,false] ++ (pairs q ++ (false::ys)))) =
      qB q (qFrontL n) ys := by
  cases q with
  | zero => simp [run,preA,qB,qFrontL,pairs,step,goL,goR]
  | succ q => simp [run,preA,qB,qFrontL,pairs,step,goL,goR]

private theorem q_core7 (m : Nat) (zs : List Bool) :
    run 7 ⟨qCoreL m,false,[true,true] ++ zs,3⟩ =
      sweepD m ([true,true,false] ++ List.replicate 6 true ++ zs) := by
  simp [run,qCoreL,sweepD,step,goL,goR,pairs,List.append_assoc]

private theorem q_phaseB (m q : Nat) (ys : List Bool):
    run (8+2*q)
      (preA (m+2) ([true,true,false] ++ (pairs q ++ (false::ys)))) =
      ⟨pairs (q+1) ++ qCoreL m,false,ys,1⟩ := by
  calc
    run (8+2*q)
        (preA (m+2) ([true,true,false] ++ (pairs q ++ (false::ys)))) =
        run (2*q)
          (run 8 (preA (m+2)
            ([true,true,false] ++ (pairs q ++ (false::ys))))) := by rw [run_add]
    _ = run (2*q) (qB q (qFrontL (m+2)) ys) := by rw [q_front8]
    _ = ⟨pairs q ++ qFrontL (m+2),false,ys,1⟩ :=
          q_b_scan q (qFrontL (m+2)) ys
    _ = ⟨pairs (q+1) ++ qCoreL m,false,ys,1⟩ := by
      congr 1
      calc
        pairs q ++ qFrontL (m+2) =
            (pairs q ++ [true,false]) ++ qCoreL m := by
              simp [qFrontL,qCoreL,List.append_assoc]
        _ = pairs (q+1) ++ qCoreL m := by rw [q_pairs_snoc]

private theorem q_twos_comm (n : Nat) (ys : List Bool) :
    List.replicate n true ++ ([true,true] ++ ys) =
      [true,true] ++ (List.replicate n true ++ ys) := by
  have ht : n+2=2+n := by omega
  calc
    List.replicate n true ++ ([true,true] ++ ys) =
        (List.replicate n true ++ List.replicate 2 true) ++ ys := by simp [List.append_assoc]
    _ = List.replicate (n+2) true ++ ys := by rw [List.replicate_append_replicate]
    _ = List.replicate (2+n) true ++ ys := by rw [ht]
    _ = (List.replicate 2 true ++ List.replicate n true) ++ ys := by
        rw [List.replicate_append_replicate]
    _ = [true,true] ++ (List.replicate n true ++ ys) := by simp [List.append_assoc]

private theorem q_phaseD (m q : Nat) (ys : List Bool):
    run (2+2*q+7) ⟨pairs (q+1) ++ qCoreL m,false,ys,1⟩ =
      sweepD m ([true,true,false] ++ List.replicate (2*q+6) true ++ ys) := by
  have ht : 2+2*q+7=2+(2*q+7) := by omega
  rw [ht,run_add]
  have hB : run 2 ⟨pairs (q+1) ++ qCoreL m,false,ys,1⟩ =
    ⟨pairs q ++ qCoreL m,false,[true,true] ++ ys,3⟩ := by
      simp [run,step,goL,goR,pairs]
  rw [hB,run_add,q_d_scan]
  rw [q_twos_comm (2*q) ys]
  change run 7 ⟨qCoreL m,false,[true,true] ++
      (List.replicate (2*q) true ++ ys),3⟩ = _
  rw [q_core7]
  have hrep : List.replicate 6 true ++ List.replicate (2*q) true =
      List.replicate (2*q+6) true := by
    calc
      List.replicate 6 true ++ List.replicate (2*q) true =
          List.replicate (6+2*q) true := List.replicate_append_replicate
      _ = List.replicate (2*q+6) true := by congr 1 <;> omega
  have hreps : List.replicate 6 true ++ (List.replicate (2*q) true ++ ys) =
      List.replicate (2*q+6) true ++ ys := by
        rw [←List.append_assoc,hrep]
  change sweepD m ([true,true,false] ++
      (List.replicate 6 true ++ (List.replicate (2*q) true ++ ys))) = _
  rw [hreps]
  simp only [List.append_assoc]

/-- Uniform 110(10)^q0 boundary: every q admits an exact right/left
    symbolic sweep, extending the earlier fixed 1100 lemma. -/
theorem two_one_pairs_front (m q : Nat) (ys : List Bool):
    run (17+4*q)
      (preA (m+2) ([true,true,false] ++ (pairs q ++ (false::ys)))) =
      sweepD m ([true,true,false] ++ List.replicate (2*q+6) true ++ ys) := by
  have ht : 17+4*q = (8+2*q)+(2+2*q+7) := by omega
  rw [ht,run_add,q_phaseB,q_phaseD]

/-- Exact all-suffix original Turing-machine return extending 1100. -/
theorem two_one_pairs_return (m q : Nat) (ys : List Bool):
    run (2*(m+2)+16+4*q)
      (preA (m+2) ([true,true,false] ++ (pairs q ++ (false::ys)))) =
    ⟨[],false,
      List.replicate (2*(m+2)+1) true ++
        (false :: List.replicate (2*q+6) true ++ ys),5⟩ := by
  have ht : 2*(m+2)+16+4*q = (17+4*q)+(2*m+3) := by omega
  rw [ht,run_add,two_one_pairs_front,sweepD_run]
  have hrep :
      List.replicate (2*m+3) true ++
        ([true,true,false] ++ List.replicate (2*q+6) true ++ ys) =
      List.replicate (2*(m+2)+1) true ++
        (false :: List.replicate (2*q+6) true ++ ys) := by
    have he : List.replicate (2*m+3) true ++ [true,true] =
        List.replicate (2*m+5) true := by
      calc
        List.replicate (2*m+3) true ++ [true,true] =
            List.replicate (2*m+3) true ++ List.replicate 2 true := by rfl
        _ = List.replicate ((2*m+3)+2) true := List.replicate_append_replicate
        _ = List.replicate (2*m+5) true := by
          rw [show (2*m+3)+2=2*m+5 by omega]
    calc
      List.replicate (2*m+3) true ++
          ([true,true,false] ++ List.replicate (2*q+6) true ++ ys) =
        (List.replicate (2*m+3) true ++ [true,true]) ++
          (false :: List.replicate (2*q+6) true ++ ys) := by
            simp [List.append_assoc]
      _ = List.replicate (2*m+5) true ++
          (false :: List.replicate (2*q+6) true ++ ys) := by rw [he]
      _ = List.replicate (2*(m+2)+1) true ++
          (false :: List.replicate (2*q+6) true ++ ys) := by
            rw [show 2*(m+2)+1=2*m+5 by omega]
  exact congrArg (fun z : List Bool => Cfg.mk [] false z 5) hrep

/-- A trajectory segment has no physical F/0 return before its endpoint.
    Here "physical" means that every cell strictly left of the head is blank. -/
def NoPhysicalF0 (c : Cfg) (n : Nat) : Prop :=
  ∀ t, t < n → ¬ Physical (run t c)

private theorem appendNoPhysicalF0 (c d : Cfg) (a b : Nat)
    (hc : NoPhysicalF0 c a) (he : run a c = d) (hd : NoPhysicalF0 d b) :
    NoPhysicalF0 c (a+b) := by
  intro t ht
  by_cases hsmall : t < a
  · exact hc t hsmall
  · obtain ⟨u,hu⟩ : ∃ u, t = a+u := ⟨t-a, by omega⟩
    rw [hu, run_add, he]
    exact hd u (by omega)

private theorem q_b_scan_noPhysical (q : Nat) (L ys : List Bool) :
    NoPhysicalF0 (qB q L ys) (2*q) := by
  induction q generalizing L ys with
  | zero =>
      intro t ht
      omega
  | succ q ih =>
      have hfirst : NoPhysicalF0 (qB (q+1) L ys) 2 := by
        intro t ht
        have hc : t=0 ∨ t=1 := by omega
        rcases hc with rfl | rfl
        all_goals simp [NoPhysicalF0, Physical, qB, run, step, goL, goR, pairs]
      have hrun : run 2 (qB (q+1) L ys) = qB q ([true,false] ++ L) ys :=
        q_b_two q L ys
      have htail : NoPhysicalF0 (qB q ([true,false] ++ L) ys) (2*q) :=
        ih ([true,false] ++ L) ys
      have h := appendNoPhysicalF0
        (qB (q+1) L ys) (qB q ([true,false] ++ L) ys) 2 (2*q)
        hfirst hrun htail
      simpa [show 2+2*q = 2*(q+1) by omega] using h

private theorem q_d_scan_noPhysical (q : Nat) (L ys : List Bool) :
    NoPhysicalF0 (⟨pairs q ++ L,false,ys,3⟩ : Cfg) (2*q) := by
  induction q generalizing L ys with
  | zero =>
      intro t ht
      omega
  | succ q ih =>
      let c : Cfg := ⟨pairs (q+1) ++ L,false,ys,3⟩
      let d : Cfg := ⟨pairs q ++ L,false,[true,true] ++ ys,3⟩
      have hfirst : NoPhysicalF0 c 2 := by
        intro t ht
        have hc : t=0 ∨ t=1 := by omega
        rcases hc with rfl | rfl
        all_goals simp [NoPhysicalF0, Physical, c, run, step, goL, goR, pairs]
      have hrun : run 2 c = d := by
        simpa [c,d] using q_d_two q L ys
      have htail : NoPhysicalF0 d (2*q) := by
        simpa [d] using ih L ([true,true] ++ ys)
      have h := appendNoPhysicalF0 c d 2 (2*q) hfirst hrun htail
      simpa [c,d,show 2+2*q = 2*(q+1) by omega] using h

/-- The first eight transitions of the 110(10)^q0 boundary cannot be a
    physical F/0 event. Any F visit in this short prefix still has a
    nonblank cell to the left. -/
private theorem q_front8_noPhysical (m q : Nat) (ys : List Bool) :
    NoPhysicalF0
      (preA (m+2) ([true,true,false] ++ (pairs q ++ (false::ys)))) 8 := by
  intro t ht
  have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ t=7 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [NoPhysicalF0, Physical, preA, run, step, goL, goR, pairs]

private theorem q_core7_noPhysical (m : Nat) (zs : List Bool) :
    NoPhysicalF0
      (⟨qCoreL m,false,[true,true] ++ zs,3⟩ : Cfg) 7 := by
  intro t ht
  have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [NoPhysicalF0, Physical, qCoreL, run, step, goL, goR, pairs]

private theorem q_phaseB_noPhysical (m q : Nat) (ys : List Bool) :
    NoPhysicalF0
      (preA (m+2) ([true,true,false] ++ (pairs q ++ (false::ys))))
      (8+2*q) := by
  apply appendNoPhysicalF0
    (preA (m+2) ([true,true,false] ++ (pairs q ++ (false::ys))))
    (qB q (qFrontL (m+2)) ys) 8 (2*q)
  · exact q_front8_noPhysical m q ys
  · exact q_front8 (m+2) q ys
  · exact q_b_scan_noPhysical q (qFrontL (m+2)) ys

private theorem q_phaseD_noPhysical (m q : Nat) (ys : List Bool) :
    NoPhysicalF0
      (⟨pairs (q+1) ++ qCoreL m,false,ys,1⟩ : Cfg)
      (2+2*q+7) := by
  let start : Cfg := ⟨pairs (q+1) ++ qCoreL m,false,ys,1⟩
  let mid : Cfg := ⟨pairs q ++ qCoreL m,false,[true,true] ++ ys,3⟩
  let mid2 : Cfg := ⟨qCoreL m,false,
      List.replicate (2*q) true ++ ([true,true] ++ ys),3⟩
  have hfirst : NoPhysicalF0 start 2 := by
    intro t ht
    have hc : t=0 ∨ t=1 := by omega
    rcases hc with rfl | rfl
    all_goals simp [NoPhysicalF0, Physical, start, run, step, goL, goR, pairs]
  have hB : run 2 start = mid := by
    simp [start,mid,run,step,goL,goR,pairs]
  have hscan : run (2*q) mid = mid2 := by
    exact q_d_scan q (qCoreL m) ([true,true] ++ ys)
  have hcore : NoPhysicalF0 mid2 7 := by
    change NoPhysicalF0
      (⟨qCoreL m,false,
        List.replicate (2*q) true ++ ([true,true] ++ ys),3⟩ : Cfg) 7
    rw [q_twos_comm (2*q) ys]
    exact q_core7_noPhysical m (List.replicate (2*q) true ++ ys)
  have htail : NoPhysicalF0 mid (2*q+7) :=
    appendNoPhysicalF0 mid mid2 (2*q) 7
      (q_d_scan_noPhysical q (qCoreL m) ([true,true] ++ ys))
      hscan hcore
  have h := appendNoPhysicalF0 start mid 2 (2*q+7) hfirst hB htail
  simpa [show 2+(2*q+7)=2+2*q+7 by omega] using h

/-- The complete 110(10)^q0 front has no earlier physical F/0 event. -/
private theorem two_one_pairs_front_noPhysical (m q : Nat) (ys : List Bool) :
    NoPhysicalF0
      (preA (m+2) ([true,true,false] ++ (pairs q ++ (false::ys))))
      (17+4*q) := by
  have hB : NoPhysicalF0
      (preA (m+2) ([true,true,false] ++ (pairs q ++ (false::ys))))
      (8+2*q) := q_phaseB_noPhysical m q ys
  have hrun : run (8+2*q)
      (preA (m+2) ([true,true,false] ++ (pairs q ++ (false::ys)))) =
      ⟨pairs (q+1) ++ qCoreL m,false,ys,1⟩ := q_phaseB m q ys
  have hD : NoPhysicalF0
      (⟨pairs (q+1) ++ qCoreL m,false,ys,1⟩ : Cfg)
      (2+2*q+7) := q_phaseD_noPhysical m q ys
  have h := appendNoPhysicalF0 _ _ (8+2*q) (2+2*q+7) hB hrun hD
  simpa [show (8+2*q)+(2+2*q+7)=17+4*q by omega] using h

/-- Strict first physical F/0 return for the all-suffix 110(10)^q0
    branch. The final D sweep is the first segment with no F state at all. -/
theorem two_one_pairs_first_physical (m q : Nat) (ys : List Bool) :
    NoPhysicalF0
      (preA (m+2) ([true,true,false] ++ (pairs q ++ (false::ys))))
      (2*(m+2)+16+4*q) := by
  have hfront : NoPhysicalF0
      (preA (m+2) ([true,true,false] ++ (pairs q ++ (false::ys))))
      (17+4*q) := two_one_pairs_front_noPhysical m q ys
  have hrun : run (17+4*q)
      (preA (m+2) ([true,true,false] ++ (pairs q ++ (false::ys)))) =
      sweepD m ([true,true,false] ++ List.replicate (2*q+6) true ++ ys) :=
    two_one_pairs_front m q ys
  have htail : NoPhysicalF0
      (sweepD m ([true,true,false] ++ List.replicate (2*q+6) true ++ ys))
      (2*m+3) := by
    intro t ht hp
    exact (CryptidBoundary.sweepD_noF m
      ([true,true,false] ++ List.replicate (2*q+6) true ++ ys) t ht) hp.1
  have h := appendNoPhysicalF0 _ _ (17+4*q) (2*m+3) hfront hrun htail
  simpa [show (17+4*q)+(2*m+3)=2*(m+2)+16+4*q by omega] using h

#print axioms two_one_pairs_first_physical

#print axioms two_one_pairs_front
#print axioms two_one_pairs_return
end BB6.CryptidBridge
