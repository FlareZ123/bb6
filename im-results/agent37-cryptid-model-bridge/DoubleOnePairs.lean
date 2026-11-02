import Lean.Elab.Tactic.Omega
import DoubleOneBranch

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

#print axioms two_one_pairs_front
#print axioms two_one_pairs_return
end BB6.CryptidBridge
