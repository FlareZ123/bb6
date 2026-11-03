import Lean.Elab.Tactic.Omega
import PrefixNoF

namespace BB6.CryptidATenFirstReturn
open CryptidBoundary
open BB6.CryptidPrefixFirstReturn
open BB6.CryptidE111FirstReturn

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

/-- Source A-on-zero boundary after the first F delimiter. -/
def aBound (m : Nat) (ys : List Bool) : Cfg :=
  ⟨false::(pairs m ++ [true,true]),false,ys,0⟩

/-- Source C-on-one leftward cursor during the final A-zero close. -/
def aCursor (m k : Nat) (ys : List Bool) : Cfg :=
  ⟨false::(pairs m ++ [true,true]),true,List.replicate k true ++ ys,2⟩

private theorem appendNoF (c d : Cfg) (a b : Nat)
    (hc : NoF c a) (he : run a c = d) (hd : NoF d b) :
    NoF c (a+b) := by
  intro t ht
  by_cases hsmall : t<a
  · exact hc t hsmall
  · have hdecomp : t=a+(t-a) := by omega
    rw [hdecomp,run_add,he]
    exact hd (t-a) (by omega)

/-- A two-symbol right token 10 pushes exactly one pair onto the left A stack. -/
theorem aTen_step (m : Nat) (ys : List Bool) :
    run 2 (aBound m ([true,false]++ys)) = aBound (m+1) ys := by
  simp [aBound,run,step,goR,pairs]

private theorem aTen_noF (m : Nat) (ys : List Bool) :
    NoF (aBound m ([true,false]++ys)) 2 := by
  intro t ht
  have hcases : t=0 ∨ t=1 := by omega
  rcases hcases with rfl | rfl
  all_goals simp [aBound,run,step,goR]

/-- Repeat the 10 token q times; this is an exact source Turing-machine run. -/
theorem aTen_run (m q : Nat) (ys : List Bool) :
    run (2*q) (aBound m (pairs q ++ ys)) =
    aBound (m+q) ys := by
  induction q generalizing m with
  | zero => simp [pairs,aBound,run]
  | succ q ih =>
    have htime : 2*(q+1)=2+2*q := by omega
    have hcode : pairs (q+1) ++ ys = [true,false] ++ (pairs q ++ ys) := by
      simp [pairs,List.append_assoc]
    rw [htime,hcode,run_add,aTen_step]
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (m+1)

private theorem aTen_noF_iter (m q : Nat) (ys : List Bool) :
    NoF (aBound m (pairs q ++ ys)) (2*q) := by
  induction q generalizing m with
  | zero =>
    intro t ht
    omega
  | succ q ih =>
    have htime : 2*(q+1)=2+2*q := by omega
    have hcode : pairs (q+1) ++ ys = [true,false] ++ (pairs q ++ ys) := by
      simp [pairs,List.append_assoc]
    rw [htime,hcode]
    have h := appendNoF
      (aBound m ([true,false]++(pairs q++ys)))
      (aBound (m+1) (pairs q++ys))
      2 (2*q) (aTen_noF m (pairs q++ys))
      (aTen_step m (pairs q++ys)) (ih (m+1))
    exact h

/-- Source two-step entry from A scanning a delimiter zero into the C cursor. -/
private theorem aClose_start (m : Nat) (ys : List Bool) :
    run 2 (aBound m (false::ys)) = aCursor m 1 ys := by
  simp [aBound,aCursor,run,step,goR,goL,pairs]

private theorem aClose_start_noF (m : Nat) (ys : List Bool) :
    NoF (aBound m (false::ys)) 2 := by
  intro t ht
  have hcases : t=0 ∨ t=1 := by omega
  rcases hcases with rfl | rfl
  all_goals simp [aBound,run,step,goR]

/-- Two steps strip one alternating pair from the left C cursor. -/
private theorem aCursor_step (m k : Nat) (ys : List Bool) :
    run 2 (aCursor (m+1) k ys) = aCursor m (k+2) ys := by
  simp [aCursor,pairs,run,step,goL,List.replicate]

private theorem aCursor_step_noF (m k : Nat) (ys : List Bool) :
    NoF (aCursor (m+1) k ys) 2 := by
  intro t ht
  have hcases : t=0 ∨ t=1 := by omega
  rcases hcases with rfl | rfl
  all_goals simp [aCursor,pairs,run,step,goL]

/-- The last pair of ones closes into a physical F0 return after four steps. -/
private theorem aCursor_base (k : Nat) (ys : List Bool) :
    run 4 (aCursor 0 k ys) =
      ⟨[],false,List.replicate (k+4) true ++ ys,5⟩ := by
  simp [aCursor,pairs,run,step,goL,List.replicate]

private theorem aCursor_base_noF (k : Nat) (ys : List Bool) :
    NoF (aCursor 0 k ys) 4 := by
  intro t ht
  have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  all_goals simp [aCursor,pairs,run,step,goL,List.replicate]

private theorem aCursor_run (m k : Nat) (ys : List Bool) :
    run (2*m+4) (aCursor m k ys) =
      ⟨[],false,List.replicate (k+2*m+4) true ++ ys,5⟩ := by
  induction m generalizing k with
  | zero => simpa using aCursor_base k ys
  | succ m ih =>
    have htime : 2*(m+1)+4=2+(2*m+4) := by omega
    rw [htime,run_add,aCursor_step]
    simpa only [show (k+2)+2*m+4=k+2*(m+1)+4 by omega] using
      (ih (k+2))

private theorem aCursor_noF (m k : Nat) (ys : List Bool) :
    NoF (aCursor m k ys) (2*m+4) := by
  induction m generalizing k with
  | zero => simpa using aCursor_base_noF k ys
  | succ m ih =>
    have htime : 2*(m+1)+4=2+(2*m+4) := by omega
    rw [htime]
    exact appendNoF
      (aCursor (m+1) k ys)
      (aCursor m (k+2) ys)
      2 (2*m+4) (aCursor_step_noF m k ys)
      (aCursor_step m k ys) (ih (k+2))

/-- The final A delimiter zero is consumed; there is no earlier F state. -/
theorem aClose_first (m : Nat) (ys : List Bool) :
    run (2*m+6) (aBound m (false::ys)) =
      ⟨[],false,List.replicate (2*m+5) true ++ ys,5⟩ ∧
    NoF (aBound m (false::ys)) (2*m+6) := by
  constructor
  · have htime : 2*m+6=2+(2*m+4) := by omega
    rw [htime,run_add,aClose_start,aCursor_run]
    congr 1
    omega
  · have htime : 2*m+6=2+(2*m+4) := by omega
    rw [htime]
    exact appendNoF
      (aBound m (false::ys)) (aCursor m 1 ys)
      2 (2*m+4) (aClose_start_noF m ys)
      (aClose_start m ys) (aCursor_noF m 1 ys)

/-- An arbitrarily long 10-only A token code followed by a zero delimiter
    gives an exactly timed first physical return for all input suffixes. -/
theorem aTenClose_first (m q : Nat) (ys : List Bool) :
    run (2*q+(2*(m+q)+6)) (aBound m (pairs q ++ false::ys)) =
      ⟨[],false,List.replicate (2*(m+q)+5) true ++ ys,5⟩ ∧
    NoF (aBound m (pairs q ++ false::ys))
      (2*q+(2*(m+q)+6)) := by
  constructor
  · rw [run_add,aTen_run]
    exact (aClose_first (m+q) ys).1
  · exact appendNoF
      (aBound m (pairs q ++ false::ys))
      (aBound (m+q) (false::ys))
      (2*q) (2*(m+q)+6)
      (aTen_noF_iter m q (false::ys))
      (aTen_run m q (false::ys))
      (aClose_first (m+q) ys).2

def aStart (k q : Nat) (ys : List Bool) : Cfg :=
  init (List.replicate (3*k+1) true ++
    false :: (pairs q ++ false::ys))

def aEnd (k q : Nat) (ys : List Bool) : Cfg :=
  ⟨[],false,List.replicate (8*k+11+2*q) true ++ ys,5⟩

/-- Two-parameter, suffix-universal source A return with strict first-positive
    physical F0 return, extending the prior endpoint-only coded A family. -/
theorem full_A_ten_first_return (k q : Nat) (ys : List Bool) :
    run (12*k*k+49*k+44+4*q) (aStart k q ys) = aEnd k q ys ∧
    ∀ t, 0<t → t<12*k*k+49*k+44+4*q →
      ¬IsPhysicalReturn (run t (aStart k q ys)) := by
  constructor
  · have htime : 12*k*k+49*k+44+4*q =
        (12*k*k+41*k+32)+(2*q+(2*((4*k+3)+q)+6)) := by omega
    rw [htime,run_add]
    have hprefix : run (12*k*k+41*k+32) (aStart k q ys) =
        aBound (4*k+3) (pairs q ++ false::ys) := by
      change run (12*k*k+41*k+32)
        (init (List.replicate (3*k+1) true ++
          false::(pairs q ++ false::ys))) = _
      rw [prefix_A]
      rfl
    rw [hprefix]
    simpa [aEnd] using (aTenClose_first (4*k+3) q ys).1
  · intro t hpos ht hphys
    by_cases hpref : t<12*k*k+41*k+32
    · exact (prefixA_positive_noF k (pairs q ++ false::ys)
        t hpos hpref) hphys.1
    · have hprefix : run (12*k*k+41*k+32) (aStart k q ys) =
          aBound (4*k+3) (pairs q ++ false::ys) := by
        change run (12*k*k+41*k+32)
          (init (List.replicate (3*k+1) true ++
            false::(pairs q ++ false::ys))) = _
        rw [prefix_A]
        rfl
      have htime : t=(12*k*k+41*k+32)+(t-(12*k*k+41*k+32)) := by omega
      have hrest : t-(12*k*k+41*k+32) <
          2*q+(2*((4*k+3)+q)+6) := by omega
      rw [htime,run_add,hprefix] at hphys
      exact (aTenClose_first (4*k+3) q ys).2
        (t-(12*k*k+41*k+32)) hrest hphys.1

#print axioms aTen_step
#print axioms aTen_run
#print axioms aClose_first
#print axioms aTenClose_first
#print axioms full_A_ten_first_return
end BB6.CryptidATenFirstReturn
