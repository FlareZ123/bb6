import Lean.Elab.Tactic.Omega
import EOneZeroHalt
import EOneTripleReturn

set_option maxRecDepth 2000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false

namespace BB6.Agent2EOneTriplePairs
open CryptidBoundary
open BB6.Agent2EOne

/-!
Two-parameter extension of the original D-start exceptional E111 return:
prepending any number of '10' pairs in front of the final 111 adds 6 primitive
steps per pair, and preserves the exact returned unary length.
-/
def rBase : List Bool :=
  [false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]

def ready0 (m : Nat) (ys : List Bool) : Cfg :=
  ⟨oppairs 6 ++ [true] ++ pairs (m+2) ++ [true,true],false,ys,0⟩

def ready (m q : Nat) (ys : List Bool) : Cfg :=
  ⟨oppairs 6 ++ oppairs q ++ [true] ++ pairs (m+2) ++ [true,true],
    false,ys,0⟩

def pivot (m left right : Nat) (ys : List Bool) : Cfg :=
  ⟨oppairs left ++ [true] ++ pairs (m+2) ++ [true,true],false,
   rBase ++ pairs right ++ ys,1⟩

theorem prefix90 (m : Nat) (ys : List Bool) :
    run 90 (startE1 m ys) = c90 m ys := by
  have h0 : 90=10+80 := by omega
  rw [h0,run_add,seg0]
  have h1 : 80=10+70 := by omega
  rw [h1,run_add,seg10]
  have h2 : 70=10+60 := by omega
  rw [h2,run_add,seg20]
  have h3 : 60=10+50 := by omega
  rw [h3,run_add,seg30]
  have h4 : 50=10+40 := by omega
  rw [h4,run_add,seg40]
  have h5 : 40=10+30 := by omega
  rw [h5,run_add,seg50]
  have h6 : 30=10+20 := by omega
  rw [h6,run_add,seg60]
  have h7 : 20=10+10 := by omega
  rw [h7,run_add,seg70]
  have h8 : 10=10+0 := by omega
  rw [h8,run_add,seg80]
  rfl

theorem seven (m : Nat) (ys : List Bool) :
    run 7 (c90 m ys) = ready0 m ys := by
  simp [c90,ready0,run,step,goL,goR,pairs,oppairs,List.append_assoc]

theorem scan2 (L ys : List Bool) :
    run 2 (⟨L,false,[true,false] ++ ys,0⟩ : Cfg) =
    ⟨[false,true] ++ L,false,ys,0⟩ := by
  simp [run,step,goL,goR]

theorem oppairs_app (q : Nat) :
    oppairs q ++ [false,true] = oppairs (q+1) := by
  induction q with
  | zero => rfl
  | succ q ih => simp [oppairs,ih,List.append_assoc]

theorem scan_pairs (q : Nat) (L ys : List Bool) :
    run (2*q) (⟨L,false,pairs q ++ ys,0⟩ : Cfg) =
      ⟨oppairs q ++ L,false,ys,0⟩ := by
  induction q generalizing L with
  | zero => simp [run,pairs,oppairs]
  | succ q ih =>
    have ht : 2*(q+1) = 2+2*q := by omega
    rw [ht,run_add]
    have h : pairs (q+1) ++ ys = [true,false] ++ (pairs q ++ ys) := by
      simp [pairs,List.append_assoc]
    rw [h]
    rw [scan2, ih]
    rw [←List.append_assoc,oppairs_app]

theorem oppairs_add (a b : Nat) :
    oppairs (a+b) = oppairs a ++ oppairs b := by
  induction a with
  | zero => simp [oppairs]
  | succ a ih =>
      simpa only [Nat.succ_add, oppairs, List.cons_append] using
        congrArg (fun xs => false::true::xs) ih

theorem oppairs_comm (a b : Nat) :
    oppairs a ++ oppairs b = oppairs b ++ oppairs a := by
  calc
    oppairs a ++ oppairs b = oppairs (a+b) := (oppairs_add a b).symm
    _ = oppairs (b+a) := by rw [Nat.add_comm]
    _ = oppairs b ++ oppairs a := oppairs_add b a

theorem scan_ready (m q : Nat) (ys : List Bool) :
    run (2*q) (ready0 m (pairs q ++ ys)) = ready m q ys := by
  unfold ready0 ready
  rw [scan_pairs]
  simpa only [List.append_assoc] using
    congrArg (fun xs => Cfg.mk xs false ys 0)
      (show oppairs q ++ (oppairs 6 ++ [true] ++ pairs (m+2) ++ [true,true]) =
        oppairs 6 ++ (oppairs q ++ [true] ++ pairs (m+2) ++ [true,true]) by
        simpa only [List.append_assoc] using
          congrArg (fun xs => xs ++ ([true] ++ pairs (m+2) ++ [true,true]))
            (oppairs_comm q 6))

/-- This 32-step phase consumes six fixed left 01 pairs and leaves the extra q. -/
theorem bridge32 (m q : Nat) (ys : List Bool) :
    run 32 (ready m q ([true,true,true] ++ ys)) =
      pivot m q 0 ys := by
  simp [ready,pivot,rBase,run,step,goL,goR,pairs,oppairs,
        List.append_assoc]

/-- A four-step left/right pair exchange. -/
theorem pump4 (m q r : Nat) (ys : List Bool) :
    run 4 (pivot m (q+1) r ys) = pivot m q (r+1) ys := by
  simp [pivot,rBase,run,step,goL,goR,pairs,oppairs,
        List.append_assoc]

theorem pump_all (m q r : Nat) (ys : List Bool) :
    run (4*q) (pivot m q r ys) = pivot m 0 (r+q) ys := by
  induction q generalizing r with
  | zero => simp [run,pivot]
  | succ q ih =>
    have ht : 4*(q+1)=4+(4*q) := by omega
    rw [ht,run_add,pump4,ih]
    congr 1
    omega

/-- Five final steps turn the pair-exchange pivot into source B sweep. -/
theorem finish5 (m q : Nat) (ys : List Bool) :
    run 5 (pivot m 0 q ys) =
      sweepB m (BB6.Agent2EOneTriple.packet ++ pairs q ++ ys) := by
  simp [pivot,rBase,BB6.Agent2EOneTriple.packet,sweepB,
        run,step,goL,goR,pairs,oppairs,List.append_assoc]

/-- Exact E-boundary closure, for arbitrary k, q and suffix. -/
theorem front_pairs (m q : Nat) (ys : List Bool) :
    run (134+6*q)
      (startE1 m (pairs q ++ ([true,true,true] ++ ys))) =
    sweepB m (BB6.Agent2EOneTriple.packet ++ pairs q ++ ys) := by
  have ht : 134+6*q = 90+(7+(2*q+(32+(4*q+5)))) := by omega
  rw [ht,run_add,prefix90,run_add,seven,run_add,scan_ready,
      run_add,bridge32,run_add,pump_all]
  simpa only [Nat.zero_add] using (finish5 m q ys)

theorem e111_pairs_run (m q : Nat) (ys : List Bool) :
    run (2*m+137+6*q)
      (startE1 m (pairs q ++ ([true,true,true] ++ ys))) =
    ⟨[],false,List.replicate (2*m+3) true ++
      (BB6.Agent2EOneTriple.packet ++ pairs q ++ ys),5⟩ := by
  have ht : 2*m+137+6*q = (134+6*q)+(2*m+3) := by omega
  rw [ht,run_add,front_pairs,sweepB_run]

theorem full_E_one_triple_pairs (k q : Nat) (ys : List Bool) :
    run (12*k*k+49*k+170+6*q)
      (init (List.replicate (3*k+2) true ++
        false :: ([true,false,true,true,false,true,true,false,false] ++
                  pairs q ++ [true,true,true] ++ ys))) =
    ⟨[],false,List.replicate (8*k+3) true ++
      (BB6.Agent2EOneTriple.packet ++ pairs q ++ ys),5⟩ := by
  have ht : 12*k*k+49*k+170+6*q =
      (12*k*k+41*k+33)+(2*(4*k)+137+6*q) := by omega
  rw [ht,run_add,prefix_E]
  change run (2*(4*k)+137+6*q)
    (startE1 (4*k) (pairs q ++ [true,true,true] ++ ys)) = _
  have hrun := e111_pairs_run (4*k) q ys
  rw [show 2*(4*k)+3=8*k+3 by omega] at hrun
  simpa only [List.append_assoc] using hrun

#print axioms scan_pairs
#print axioms bridge32
#print axioms pump4
#print axioms front_pairs
#print axioms full_E_one_triple_pairs
end BB6.Agent2EOneTriplePairs
