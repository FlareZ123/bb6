import Lean.Elab.Tactic.Omega
import CryptidPairs
import A1100

namespace BB6.Agent35PairTerminal
open CryptidBoundary
set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

/-- Reverse sweep over alternating left stack, with the head scanning one. -/
def back (n : Nat) (L ys : List Bool) : Cfg :=
    ⟨oppairs n ++ L,true,true::ys,0⟩

/-- Four original six-state primitive moves consume one left alternating pair. -/
theorem back_four (n : Nat) (L ys : List Bool) :
    run 4 (back (n+1) L ys) =
       back n L ([true,false] ++ ys) := by
  simp [back,oppairs,run,step,goL,goR,List.append_assoc]

private theorem pairs_snoc (n : Nat) :
    pairs n ++ [true,false] = [true,false] ++ pairs n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [pairs,List.append_assoc] using
      congrArg (fun zs : List Bool => [true,false] ++ zs) ih

/-- Unbounded reverse sweep converts every crossed 01 pair into a rightward 10 pair. -/
theorem back_run (n : Nat) (L ys : List Bool) :
    run (4*n) (back n L ys) = back 0 L (pairs n ++ ys) := by
  induction n generalizing ys with
  | zero => rfl
  | succ n ih =>
    have ht : 4*(n+1)=4+4*n := by omega
    rw [ht,run_add,back_four,ih]
    simp only [pairs,List.append_assoc]
    rw [pairs_snoc]

/-- Single-step source certificate of the seven-move A turn. -/
private theorem front_seven_raw (L Z : List Bool) :
    run 7 (⟨false::L,false,[true,true,false,true] ++ Z,0⟩ : Cfg) =
      ⟨[false,true,true,false] ++ L,false,true::Z,0⟩ := by
  let c0 : Cfg := ⟨false::L,false,[true,true,false,true] ++ Z,0⟩
  let c1 : Cfg := ⟨true::false::L,true,[true,false,true] ++ Z,1⟩
  let c2 : Cfg := ⟨false::true::false::L,true,[false,true] ++ Z,0⟩
  let c3 : Cfg := ⟨false::false::true::false::L,false,true::Z,4⟩
  let c4 : Cfg := ⟨false::true::false::L,false,[false,true] ++ Z,2⟩
  let c5 : Cfg := ⟨true::false::L,false,[true,false,true] ++ Z,0⟩
  let c6 : Cfg := ⟨true::true::false::L,true,[false,true] ++ Z,1⟩
  let c7 : Cfg := ⟨false::true::true::false::L,false,true::Z,0⟩
  have h1 : step c0 = c1 := by rfl
  have h2 : step c1 = c2 := by rfl
  have h3 : step c2 = c3 := by rfl
  have h4 : step c3 = c4 := by rfl
  have h5 : step c4 = c5 := by rfl
  have h6 : step c5 = c6 := by rfl
  have h7 : step c6 = c7 := by rfl
  change run 7 c0 = c7
  simp only [run,h1,h2,h3,h4,h5,h6,h7]

private theorem head_swap (j : Nat) (ys : List Bool) :
    true :: (oppairs j ++ ys) = pairs j ++ (true :: ys) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simpa [oppairs,pairs,List.append_assoc] using
      congrArg (fun zs : List Bool => true :: false :: zs) ih

/-- Initial constant-size A turn enters the forward scanner. -/
theorem front_seven (m j : Nat) (ys : List Bool) :
    run 7
      (aBoundary m
        ([true,true] ++ (oppairs (j+1) ++ ([true,true] ++ ys)))) =
    scanStart j
      (oppairs 1 ++ (pairs (m+1) ++ [true,true]))
      ([true,true,true] ++ ys) := by
  have hin : aBoundary m
        ([true,true] ++ (oppairs (j+1) ++ ([true,true] ++ ys))) =
      (⟨false::(pairs m ++ [true,true]),false,
        [true,true,false,true] ++ (oppairs j ++ ([true,true] ++ ys)),0⟩ : Cfg) := by
    simp [aBoundary,oppairs,List.append_assoc]
  have hout :
      (⟨[false,true,true,false] ++ (pairs m ++ [true,true]),
        false,true::(oppairs j ++ ([true,true] ++ ys)),0⟩ : Cfg) =
      scanStart j
        (oppairs 1 ++ (pairs (m+1) ++ [true,true]))
        ([true,true,true] ++ ys) := by
    simp only [scanStart,oppairs,pairs,List.cons_append]
    have hs := head_swap j ([true,true] ++ ys)
    simpa [List.append_assoc] using hs
  rw [hin]
  exact (front_seven_raw (pairs m ++ [true,true])
      (oppairs j ++ ([true,true] ++ ys))).trans hout

private theorem oppairs_snoc (n : Nat) :
    oppairs n ++ [false,true] = oppairs (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [oppairs,List.append_assoc] using
      congrArg (fun zs : List Bool => [false,true] ++ zs) ih

private theorem oppairs_comm (j : Nat) :
    [false,true] ++ oppairs j = oppairs j ++ [false,true] := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simpa [oppairs,List.append_assoc] using
      congrArg (fun zs : List Bool => [false,true] ++ zs) ih

/-- The constant two-step turn on the triple-one suffix. -/
private theorem turn_two_raw (L ys : List Bool) :
    run 2 (⟨L,false,[true,true,true] ++ ys,0⟩ : Cfg) =
      ⟨[false,true] ++ L,true,true::ys,0⟩ := by
  rfl

/-- The scanner converts the right triple-one end into a reversible left stack. -/
theorem turn_two (m j : Nat) (ys : List Bool) :
    run 2
      (⟨oppairs j ++ (oppairs 1 ++ (pairs (m+1) ++ [true,true])),
        false,[true,true,true] ++ ys,0⟩ : Cfg) =
    back (j+2) (pairs (m+1) ++ [true,true]) ys := by
  rw [turn_two_raw]
  change (⟨[false,true] ++
      (oppairs j ++ (oppairs 1 ++ (pairs (m+1) ++ [true,true]))),
      true,true::ys,0⟩ : Cfg) =
    ⟨oppairs (j+2) ++ (pairs (m+1) ++ [true,true]),
      true,true::ys,0⟩
  congr 1
  calc
    _ = (oppairs j ++ [false,true]) ++
          ([false,true] ++ (pairs (m+1) ++ [true,true])) := by
            rw [←List.append_assoc,oppairs_comm j]
            simp [oppairs,List.append_assoc]
    _ = oppairs (j+2) ++ (pairs (m+1) ++ [true,true]) := by
      rw [oppairs_snoc,←List.append_assoc,oppairs_snoc]

/-- Four source primitive steps consume the final left pair and enter D. -/
private theorem back_base_raw (L Z : List Bool) :
    run 4 (⟨true::false::L,true,true::Z,0⟩ : Cfg) =
      ⟨L,false,[true,true,false] ++ Z,3⟩ := by
  let c0 : Cfg := ⟨true::false::L,true,true::Z,0⟩
  let c1 : Cfg := ⟨false::true::false::L,true,Z,4⟩
  let c2 : Cfg := ⟨true::false::L,false,false::Z,1⟩
  let c3 : Cfg := ⟨false::L,true,true::false::Z,2⟩
  let c4 : Cfg := ⟨L,false,[true,true,false] ++ Z,3⟩
  have h1 : step c0 = c1 := by rfl
  have h2 : step c1 = c2 := by rfl
  have h3 : step c2 = c3 := by rfl
  have h4 : step c3 = c4 := by rfl
  change run 4 c0 = c4
  simp only [run,h1,h2,h3,h4]

theorem back_base (m j : Nat) (ys : List Bool) :
    run 4
      (back 0 (pairs (m+1) ++ [true,true]) (pairs (j+2) ++ ys)) =
    sweepD m ([true,true,false] ++ (pairs (j+2) ++ ys)) := by
  simpa [back,oppairs,sweepD,pairs,List.append_assoc] using
    back_base_raw (pairs m ++ [true,true]) (pairs (j+2) ++ ys)

/-- Arbitrarily many alternating terminal pairs, exactly 6 primitive moves per pair. -/
theorem a_many_front (m j : Nat) (ys : List Bool) :
    run (6*j+21)
      (aBoundary m
        ([true,true] ++ (oppairs (j+1) ++ ([true,true] ++ ys)))) =
    sweepD m ([true,true,false] ++ (pairs (j+2) ++ ys)) := by
  have ht : 6*j+21=7+(2*j+(2+(4*(j+2)+4))) := by omega
  rw [ht,run_add,run_add,run_add,run_add,front_seven,scan_run]
  change run 4 (run (4*(j+2))
      (back (j+2) (pairs (m+1) ++ [true,true]) ys)) = _
  rw [back_run]
  exact back_base m j ys

/-- ALL j≥1 original-source A terminal 11(01)^j11, exact primitive runtime. -/
theorem a_many_pairs_return (m j : Nat) (ys : List Bool) :
    run (2*m+6*j+24)
      (aBoundary m
        ([true,true] ++ (oppairs (j+1) ++ ([true,true] ++ ys)))) =
    (⟨[],false,
      List.replicate (2*m+5) true ++
        (false :: (pairs (j+2) ++ ys)),5⟩ : Cfg) := by
  have ht : 2*m+6*j+24=(6*j+21)+(2*m+3) := by omega
  rw [ht,run_add,a_many_front,sweepD_run]
  have hn : List.replicate (2*m+3) true ++ [true,true] =
      List.replicate (2*m+5) true := by
    rw [←List.replicate_append_replicate]
    congr 1
    omega
  simp [List.append_assoc,hn]

#print axioms back_four
#print axioms back_run
#print axioms front_seven
#print axioms turn_two
#print axioms a_many_front
#print axioms a_many_pairs_return
end BB6.Agent35PairTerminal
