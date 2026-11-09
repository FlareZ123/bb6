import Lean.Elab.Tactic.Omega
import EZeroPair

namespace BB6.Agent36EZeroZTwo
open CryptidBoundary
open BB6.Agent32EZero

set_option maxRecDepth 8192
set_option maxHeartbeats 10000000

/-- Source E boundary with a zero-ended, arbitrarily long 10-pair tail. -/
def eZeroPairs (u r : Nat) (ys : List Bool) : Cfg :=
  ⟨false::false::pairs (u+3) ++ [true,true],false,
    [true,true,false] ++ (pairs r ++ (false::ys)),4⟩

private def coreLeft (u : Nat) : List Bool :=
  [false,true,true,false,true,true,false,true] ++ oppairs (u+2) ++ [true]

private theorem pair_end (u : Nat) :
    pairs u ++ [true,true] = true :: (oppairs u ++ [true]) := by
  induction u with
  | zero => rfl
  | succ u ih =>
    simpa [pairs, oppairs, List.append_assoc] using congrArg (fun z => true :: false :: z) ih

private theorem front11 (u r : Nat) (ys : List Bool) :
    run 11 (eZeroPairs u r ys) =
      (⟨coreLeft u,false,pairs r ++ (false::ys),0⟩ : Cfg) := by
  simp [eZeroPairs, coreLeft, run,step,goL,goR,pairs,List.append_assoc]
  rw [pair_end]
  simp [oppairs, List.append_assoc]

private theorem base11 (u r : Nat) (ys : List Bool) :
    run 11 (eZero u (List.replicate (2*r) true ++ ys)) =
      (⟨coreLeft u,false,false::(List.replicate (2*r) true ++ ys),0⟩ : Cfg) := by
  simp [eZero,coreLeft,run,step,goL,goR,pairs,List.append_assoc]
  rw [pair_end]
  simp [oppairs, List.append_assoc]

private theorem a_pair_two (r : Nat) (L ys : List Bool) :
    run 2 (⟨L,false,pairs (r+1) ++ ys,0⟩ : Cfg) =
      ⟨[false,true] ++ L,false,pairs r ++ ys,0⟩ := by
  simp [run,step,goL,goR,pairs]

private theorem oppairs_snoc (r : Nat) :
    oppairs r ++ [false,true] = oppairs (r+1) := by
  induction r with
  | zero => rfl
  | succ r ih => simp [oppairs,ih,List.append_assoc]

private theorem a_pair_scan (r : Nat) (L ys : List Bool) :
    run (2*r) (⟨L,false,pairs r ++ ys,0⟩ : Cfg) =
      ⟨oppairs r ++ L,false,ys,0⟩ := by
  induction r generalizing L with
  | zero => rfl
  | succ r ih =>
    have ht : 2*(r+1)=2+(2*r) := by omega
    rw [ht,run_add,a_pair_two,ih]
    congr 1
    calc
      oppairs r ++ ([false,true] ++ L) =
        (oppairs r ++ [false,true]) ++ L := by simp [List.append_assoc]
      _ = oppairs (r+1) ++ L := by rw [oppairs_snoc]

private theorem a_zero_two (L ys : List Bool) :
    run 2 (⟨L,false,false::ys,0⟩ : Cfg) =
      ⟨L,true,true::ys,2⟩ := by
  simp [run,step,goL,goR]

private theorem c_pair_two (r : Nat) (L ys : List Bool) :
    run 2 (⟨oppairs (r+1) ++ L,true,ys,2⟩ : Cfg) =
      ⟨oppairs r ++ L,true,[true,true] ++ ys,2⟩ := by
  simp [run,step,goL,goR,oppairs]

private theorem c_pair_scan (r : Nat) (L ys : List Bool) :
    run (2*r) (⟨oppairs r ++ L,true,ys,2⟩ : Cfg) =
      ⟨L,true,List.replicate (2*r) true ++ ys,2⟩ := by
  induction r generalizing ys with
  | zero => rfl
  | succ r ih =>
    have ht : 2*(r+1)=2+(2*r) := by omega
    rw [ht,run_add,c_pair_two,ih]
    have hr : List.replicate (2*r) true ++ ([true,true] ++ ys) =
        List.replicate (2+2*r) true ++ ys := by
      calc
        _ = (List.replicate (2*r) true ++ List.replicate 2 true) ++ ys := by
          simp [List.append_assoc]
        _ = _ := by
          rw [List.replicate_append_replicate]
          simp only [show 2*r+2=2+2*r by omega]
    exact congrArg (fun z : List Bool => (⟨L,true,z,2⟩ : Cfg)) hr

private theorem all_pairs_13 (u r : Nat) (ys : List Bool) :
    run (13+4*r) (eZeroPairs u r ys) =
      run 13 (eZero u (List.replicate (2*r) true ++ ys)) := by
  have ht : 13+4*r = 11+(2*r+(2+2*r)) := by omega
  rw [ht,run_add,front11]
  rw [run_add,a_pair_scan]
  rw [run_add,a_zero_two]
  rw [c_pair_scan]
  have hcomm : List.replicate (2*r) true ++ (true::ys) =
    true :: (List.replicate (2*r) true ++ ys) := by
    induction (2*r) with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ,ih]
  rw [hcomm]
  have hb : run 13 (eZero u (List.replicate (2*r) true ++ ys)) =
    ⟨coreLeft u,true,true::(List.replicate (2*r) true ++ ys),2⟩ := by
    rw [show (13:Nat)=11+2 by omega,run_add,base11,a_zero_two]
  exact hb.symm

/-- The q=0 E/110 terminal is uniformly stable under any number
    of inserted 10 pairs, at an exact additional cost of four per pair. -/
theorem e_zero_pairs_all (u r : Nat) (ys : List Bool) :
    run (2*u+63+4*r) (eZeroPairs u r ys) =
      ⟨[],false,List.replicate (2*u+3) true ++
        (packetZero ++ (List.replicate (2*r) true ++ ys)),5⟩ := by
  have ht : 2*u+63+4*r = (13+4*r)+(2*u+50) := by omega
  rw [ht,run_add,all_pairs_13]
  have ht2 : 2*u+63 = 13+(2*u+50) := by omega
  have hr := eZero_run u (List.replicate (2*r) true ++ ys)
  rw [ht2,run_add] at hr
  exact hr

/-- Original six-state F/0-to-F/0 source equality for all k,r and
    every unrestricted finite suffix, without padding normalization. -/
theorem full_E_zero_pairs_all (k r : Nat) (ys : List Bool) :
    run (12*k*k+49*k+96+4*r)
      (init (List.replicate (3*k+2) true ++
        false :: ([true,true,false] ++ (pairs r ++ (false::ys))))) =
    ⟨[],false,List.replicate (8*k+3) true ++
      (packetZero ++ (List.replicate (2*r) true ++ ys)),5⟩ := by
  have ht : 12*k*k+49*k+96+4*r =
    (12*k*k+41*k+33)+(2*(4*k)+63+4*r) := by omega
  rw [ht,run_add,prefix_E]
  change run (2*(4*k)+63+4*r) (eZeroPairs (4*k) r ys) = _
  rw [e_zero_pairs_all]
  rw [show 2*(4*k)+3=8*k+3 by omega]

#print axioms all_pairs_13
#print axioms e_zero_pairs_all
#print axioms full_E_zero_pairs_all
end BB6.Agent36EZeroZTwo
