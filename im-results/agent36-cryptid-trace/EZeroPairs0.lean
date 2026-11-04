import Lean.Elab.Tactic.Omega
import EDoubleTripleGeneral

namespace BB6.Agent36EZeroPairs0
open CryptidBoundary
set_option maxHeartbeats 10000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

def leftCarrier (m : Nat) : List Bool :=
  oppairs 1 ++ (pairs (m+3) ++ [true,true])

def packetZero : List Bool :=
  [false,true,true,true,true,false,true,false,true,false,true,false]

def ePairZero (m r : Nat) (ys : List Bool) : Cfg :=
  ⟨false::false::pairs (m+3) ++ [true,true],false,
    [true,true,false] ++ (pairs r ++ (false::ys)),4⟩

/-- The first E detour uses four raw instructions. -/
theorem e_four (m r : Nat) (ys : List Bool) :
    run 4 (ePairZero m r ys) =
      ⟨leftCarrier m,false,
        [true,true,false] ++ (pairs r ++ (false::ys)),0⟩ := by
  simp [ePairZero,leftCarrier,run,step,goL,goR,pairs,oppairs]

/-- The seven-step A turn reverses the first marked cell of the left stack. -/
theorem a_seven (L zs : List Bool) :
    run 7 (⟨false::L,false,[true,true,false] ++ zs,0⟩ : Cfg) =
      ⟨[false,true,true,false] ++ L,false,zs,0⟩ := by
  simp [run,step,goL,goR]

theorem a_pair_run (r : Nat) (L ys : List Bool) :
    run (2*r) (⟨L,false,pairs r ++ ys,0⟩ : Cfg) =
      ⟨oppairs r ++ L,false,ys,0⟩ := by
  exact aTenOppIter r L ys

private theorem shifted (r : Nat) (L : List Bool) :
    oppairs r ++ ([false,true,true] ++ L) =
      false :: (pairs r ++ ([true,true] ++ L)) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simpa only [oppairs,pairs,List.cons_append,List.nil_append,List.append_assoc] using
      congrArg (fun z : List Bool => [false,true] ++ z) ih

/-- Three steps after the forward A token scan expose r reversed D pairs. -/
theorem a_three (r : Nat) (L ys : List Bool) :
    run 3 (⟨oppairs r ++ ([false,true,true] ++ L),
      false,false::ys,0⟩ : Cfg) =
    ⟨pairs r ++ ([true,true] ++ L),false,[true,true] ++ ys,3⟩ := by
  rw [shifted]
  simp [run,step,goL,goR]

private theorem d_pair_two (r : Nat) (L ys : List Bool) :
    run 2 (⟨pairs (r+1) ++ L,false,ys,3⟩ : Cfg) =
      ⟨pairs r ++ L,false,[true,true] ++ ys,3⟩ := by
  simp [run,step,goL,goR,pairs]

theorem d_pair_run (r : Nat) (L ys : List Bool) :
    run (2*r) (⟨pairs r ++ L,false,ys,3⟩ : Cfg) =
      ⟨L,false,List.replicate (2*r) true ++ ys,3⟩ := by
  induction r generalizing ys with
  | zero => simp [run,pairs]
  | succ r ih =>
    have ht : 2*(r+1)=2+2*r := by omega
    rw [ht,run_add,d_pair_two,ih]
    have hrep : List.replicate (2*r) true ++ ([true,true] ++ ys) =
      List.replicate (2*(r+1)) true ++ ys := by
      calc
        _ = (List.replicate (2*r) true ++ List.replicate 2 true) ++ ys := by
          simp only [List.replicate_succ,List.replicate_zero,
            List.cons_append,List.nil_append,List.append_assoc]
        _ = List.replicate (2*r+2) true ++ ys := by
          rw [←List.replicate_append_replicate]
        _ = List.replicate (2*(r+1)) true ++ ys := by
          rw [show 2*r+2=2*(r+1) by omega]
    simpa only [show 2*(r+1)=2+2*r by omega] using
      (congrArg (fun zs : List Bool => Cfg.mk L false zs 3) hrep)

theorem d_two (L ys : List Bool) :
    run 2 (⟨[true,true] ++ L,false,ys,3⟩ : Cfg) =
      ⟨L,true,[true,true] ++ ys,3⟩ := by
  simp [run,step,goL,goR]

/-- The fixed final 44 instructions preserve all unknown trailing bits. -/
theorem d_tail44 (m : Nat) (ys : List Bool) :
    run 44 (⟨leftCarrier m,true,[true,true,true,true] ++ ys,3⟩ : Cfg) =
      sweepB m (packetZero ++ ys) := by
  simp [leftCarrier,packetZero,sweepB,run,step,goL,goR,pairs,oppairs]

/-- All r forward 10-packets and all reverse D-packets compose in 16+4r. -/
theorem e_to_d (m r : Nat) (ys : List Bool) :
    run (16+4*r) (ePairZero m r ys) =
      ⟨leftCarrier m,true,List.replicate (2*r+4) true ++ ys,3⟩ := by
  have ht : 16+4*r = 4+(7+(2*r+(3+(2*r+2)))) := by omega
  rw [ht,run_add,e_four]
  change run (7+(2*r+(3+(2*r+2))))
    (⟨false::(true::(pairs (m+3) ++ [true,true])),false,
      [true,true,false] ++ (pairs r ++ (false::ys)),0⟩ : Cfg) = _
  rw [run_add,a_seven]
  change run (2*r+(3+(2*r+2)))
    (⟨[false,true,true] ++ leftCarrier m,false,
      pairs r ++ (false::ys),0⟩ : Cfg) = _
  rw [run_add,a_pair_run]
  rw [run_add,a_three]
  rw [run_add,d_pair_run]
  rw [d_two]
  have hrep : [true,true] ++
      (List.replicate (2*r) true ++ ([true,true] ++ ys)) =
      List.replicate (2*r+4) true ++ ys := by
    calc
      _ = (List.replicate 2 true ++ List.replicate (2*r) true ++
          List.replicate 2 true) ++ ys := by
        simp only [List.replicate_succ,List.replicate_zero,
          List.cons_append,List.nil_append,List.append_assoc]
      _ = List.replicate (2+2*r+2) true ++ ys := by
        rw [←List.replicate_append_replicate,←List.replicate_append_replicate]
      _ = _ := by
        rw [show 2+2*r+2=2*r+4 by omega]
  exact congrArg (fun zs : List Bool =>
    Cfg.mk (leftCarrier m) true zs 3) hrep

/-- Uniform E-to-B boundary extension, r additional forward packets. -/
theorem e_to_b (m r : Nat) (ys : List Bool) :
    run (60+4*r) (ePairZero m r ys) =
      sweepB m (packetZero ++ (List.replicate (2*r) true ++ ys)) := by
  have ht : 60+4*r = (16+4*r)+44 := by omega
  rw [ht,run_add,e_to_d]
  have hp : List.replicate (2*r+4) true ++ ys =
      [true,true,true,true] ++ (List.replicate (2*r) true ++ ys) := by
    rw [show 2*r+4=4+2*r by omega]
    rw [←List.replicate_append_replicate]
    simp only [List.replicate_succ,List.replicate_zero,
      List.cons_append,List.nil_append,List.append_assoc]
  rw [hp,d_tail44]

/-- Complete actual E return on 110(10)^r0, arbitrary r,m,right continuation. -/
theorem e_pair_zero_run (m r : Nat) (ys : List Bool) :
    run (2*m+4*r+63) (ePairZero m r ys) =
      ⟨[],false,List.replicate (2*m+3) true ++
        (packetZero ++ (List.replicate (2*r) true ++ ys)),5⟩ := by
  have ht : 2*m+4*r+63 = (60+4*r)+(2*m+3) := by omega
  rw [ht,run_add,e_to_b,sweepB_run]

/-- Entire original-source F return for E class and all r. -/
theorem full_E_110_pairs_zero (k r : Nat) (ys : List Bool) :
    run (12*k*k+49*k+96+4*r)
      (init (List.replicate (3*k+2) true ++
        false :: ([true,true,false] ++ (pairs r ++ (false::ys))))) =
      ⟨[],false,List.replicate (8*k+3) true ++
        (packetZero ++ (List.replicate (2*r) true ++ ys)),5⟩ := by
  have ht : 12*k*k+49*k+96+4*r =
    (12*k*k+41*k+33)+(2*(4*k)+4*r+63) := by omega
  rw [ht,run_add,prefix_E]
  change run (2*(4*k)+4*r+63) (ePairZero (4*k) r ys) = _
  rw [e_pair_zero_run]
  rw [show 2*(4*k)+3=8*k+3 by omega]

#print axioms a_three
#print axioms d_pair_run
#print axioms e_to_d
#print axioms e_to_b
#print axioms full_E_110_pairs_zero

end BB6.Agent36EZeroPairs0
