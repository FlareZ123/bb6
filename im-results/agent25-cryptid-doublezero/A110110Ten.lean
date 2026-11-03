import Lean.Elab.Tactic.Omega
import A1101100

namespace CryptidBoundary
set_option maxHeartbeats 5000000
set_option maxRecDepth 2048
set_option linter.unusedSimpArgs false

def bRead (l ws : List Bool) : Cfg :=
  ⟨l,ws.headD false,ws.drop 1,1⟩

def baseL110110 (m : Nat) : List Bool :=
  [true,false,true,true,false,true,true,false] ++ pairs (m+3) ++ [true,true]

def bZero (l ys : List Bool) : Cfg := ⟨l,false,ys,1⟩

theorem pairs_snoc (q : Nat) : pairs (q+1) = pairs q ++ [true,false] := by
  induction q with
  | zero => simp [pairs]
  | succ q ih => simpa [pairs] using ih

theorem bRead_cons (l ws : List Bool) :
    run 2 (bRead l (true::false::ws)) = bRead (true::false::l) ws := by
  cases ws with
  | nil => simp [bRead,run,step,goR,goL]
  | cons x xs => simp [bRead,run,step,goR,goL]

theorem bConsume (q : Nat) (l ys : List Bool) :
    run (2*q) (bRead l (pairs q ++ false::ys)) =
      bZero (pairs q ++ l) ys := by
  induction q generalizing l with
  | zero => simp [bRead,bZero,pairs,run]
  | succ q ih =>
    have ht : 2*(q+1) = 2+2*q := by omega
    rw [ht,run_add]
    have hfirst : run 2 (bRead l (pairs (q+1) ++ false::ys)) =
        bRead (true::false::l) (pairs q ++ false::ys) := by
      simpa [pairs] using bRead_cons l (pairs q ++ false::ys)
    rw [hfirst, ih]
    simp only [bZero]
    congr 1
    simp [pairs_snoc, List.append_assoc]

theorem bZero_strip_three (q : Nat) (l ys : List Bool) :
    run 3 (bZero (pairs (q+1) ++ l) ys) =
      run 1 (bZero (pairs q ++ l) (true::true::ys)) := by
  simp [bZero,pairs,run,step,goL,goR,List.append_assoc]

theorem bZero_strip (q : Nat) (l ys : List Bool) :
    run (2*q+1) (bZero (pairs q ++ l) ys) =
      run 1 (bZero l (List.replicate (2*q) true ++ ys)) := by
  induction q generalizing ys with
  | zero => simp [pairs]
  | succ q ih =>
    have ht : 2*(q+1)+1 = 3+2*q := by omega
    rw [ht,run_add,bZero_strip_three]
    have hjoin : run (2*q) (run 1 (bZero (pairs q ++ l) (true::true::ys))) =
        run (2*q+1) (bZero (pairs q ++ l) (true::true::ys)) := by
      simpa only [show 1+2*q=2*q+1 by omega] using
        (run_add 1 (2*q) (bZero (pairs q ++ l) (true::true::ys))).symm
    rw [hjoin, ih]
    apply congrArg (fun c : Cfg => run 1 c)
    simp only [bZero]
    congr 1
    rw [show 2*(q+1)=2*q+2 by omega, ←List.replicate_append_replicate]
    simp [List.append_assoc]

/-- Exact 50-step terminal transition from the B-on-zero pattern. -/
theorem bZero_base50 (m : Nat) (ys : List Bool) :
    run 50 (bZero (baseL110110 m) ys) =
       sweepD m (true::true::terminal1101100tail ys) := by
  simp [bZero,baseL110110,sweepD,terminal1101100tail,
    run,step,goL,goR,pairs]

/-- An arbitrary stack of 10 pairs costs four extra primitive steps per pair,
    and deposits two unary ones on the terminal right suffix. -/
theorem bZero_q50 (m q : Nat) (ys : List Bool) :
    run (2*q+50) (bZero (pairs q ++ baseL110110 m) ys) =
      sweepD m (true::true::terminal1101100tail
        (List.replicate (2*q) true ++ ys)) := by
  have ht : 2*q+50 = (2*q+1)+49 := by omega
  rw [ht,run_add,bZero_strip]
  have hh := bZero_base50 m (List.replicate (2*q) true ++ ys)
  rw [show 50=1+49 by omega,run_add] at hh
  exact hh

/-- First 15 raw steps reach state B reading the untouched suffix after 110110. -/
theorem a110110_prefix15 (m q : Nat) (ys : List Bool) :
    run 15 (aBoundary (m+3)
      (true::true::false::true::true::false::(pairs q ++ false::ys))) =
    bRead (baseL110110 m) (pairs q ++ false::ys) := by
  cases q with
  | zero => simp [aBoundary,baseL110110,bRead,pairs,run,step,goL,goR]
  | succ q => simp [aBoundary,baseL110110,bRead,pairs,run,step,goL,goR]

/-- For every m and q, same final sweepD with a 4q time penalty. -/
theorem a110110_ten_to_sweep (m q : Nat) (ys : List Bool) :
    run (65+4*q) (aBoundary (m+3)
      (true::true::false::true::true::false::(pairs q ++ false::ys))) =
    sweepD m (true::true::terminal1101100tail
      (List.replicate (2*q) true ++ ys)) := by
  have ht : 65+4*q = 15+(2*q+(2*q+50)) := by omega
  rw [ht,run_add,a110110_prefix15,run_add,bConsume,bZero_q50]

/-- Exact F-on-zero return for every A-110110(10)^q0 cylinder. -/
theorem full_A_110110_ten (k q : Nat) (ys : List Bool) :
    run (12*k*k+49*k+100+4*q)
      (init (List.replicate (3*k+1) true ++
        false::true::true::false::true::true::false::(pairs q ++ false::ys))) =
      ⟨[],false,List.replicate (8*k+5) true ++ terminal1101100tail
        (List.replicate (2*q) true ++ ys),5⟩ := by
  have ht : 12*k*k+49*k+100+4*q =
      (12*k*k+41*k+32) + ((65+4*q)+(2*(4*k)+3)) := by omega
  rw [ht,run_add,prefix_A]
  change run ((65+4*q)+(2*(4*k)+3)) (aBoundary (4*k+3)
    (true::true::false::true::true::false::(pairs q ++ false::ys))) = _
  rw [run_add,a110110_ten_to_sweep,sweepD_run]
  apply congrArg (fun zs : List Bool => (⟨[],false,zs,5⟩ : Cfg))
  calc
    List.replicate (2*(4*k)+3) true ++
        true::true::terminal1101100tail (List.replicate (2*q) true ++ ys) =
      (List.replicate (2*(4*k)+3) true ++ List.replicate 2 true) ++
        terminal1101100tail (List.replicate (2*q) true ++ ys) := by
          simp [List.append_assoc]
    _ = List.replicate (2*(4*k)+3+2) true ++
        terminal1101100tail (List.replicate (2*q) true ++ ys) := by
          rw [List.replicate_append_replicate]
    _ = _ := by rw [show 2*(4*k)+3+2=8*k+5 by omega]

#print axioms bZero_q50
#print axioms a110110_ten_to_sweep
#print axioms full_A_110110_ten
end CryptidBoundary
