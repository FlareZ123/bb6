import Lean.Elab.Tactic.Omega
import EZeroZTwoA
import BoundaryBZero
import BoundaryPadding
import PacketSource

namespace BB6.Agent36EZeroZTwoAll
open CryptidBoundary
open BB6.Agent36EZeroZTwoFollow
open BB6.Agent36EZeroZTwoA
open BB6.Agent2BoundaryBZero
open BB6.BoundaryPadding BB6.Padding

set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

private theorem oppairs_end (q : Nat) :
    oppairs (q+1) = oppairs q ++ [false,true] := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simpa only [oppairs,List.cons_append] using
      congrArg (fun xs : List Bool => false :: true :: xs) ih

/-- The terminal zero on an alternating packet is physically blank.
    For a nonzero marker, the following unary tail completes one more 01 pair. -/
private theorem tail_regular (a q m : Nat) :
    ∃ p b, ObsEq
      (⟨[],false,List.replicate a true ++
        ((oppairs q ++ [false]) ++ List.replicate (2*m) true),5⟩ : Cfg)
      (regularSection a p b) := by
  cases m with
  | zero =>
    refine ⟨q,0,?_⟩
    have h := source_pad 0 0 1 (regularSection a q 0)
    change ObsEq
      (regularSection a q 0)
      (⟨[],false,(List.replicate a true ++ (oppairs q ++ [])) ++ [false],5⟩ : Cfg) at h
    simpa [ObsEq,regularSection,run,List.append_assoc] using (cfgEq_symm h)
  | succ m =>
    refine ⟨q+1,2*m+1,?_⟩
    have hr : List.replicate (2*(m+1)) true =
        true :: List.replicate (2*m+1) true := by
      rw [show 2*(m+1)=(2*m+1)+1 by omega, List.replicate_succ]
    have hc :
        (⟨[],false,List.replicate a true ++
           ((oppairs q ++ [false]) ++ List.replicate (2*(m+1)) true),5⟩ : Cfg) =
           regularSection a (q+1) (2*m+1) := by
      simp [regularSection,hr,oppairs_end,List.append_assoc]
    rw [hc]
    simpa [ObsEq,run] using (source_pad 0 0 0 (regularSection a (q+1) (2*m+1)))

private theorem tail7_regular (a m : Nat) :
    ∃ q b, ObsEq
      (⟨[],false,List.replicate a true ++
        (tail7 ++ List.replicate (2*m) true),5⟩ : Cfg)
      (regularSection a q b) := by
  simpa [tail7,oppairs] using tail_regular a 3 m

private theorem tail13_regular (a m : Nat) :
    ∃ q b, ObsEq
      (⟨[],false,List.replicate a true ++
        (tail13 ++ List.replicate (2*m) true),5⟩ : Cfg)
      (regularSection a q b) := by
  simpa [tail13,oppairs] using tail_regular a 6 m

private theorem branch_B (t m : Nat) :
    ∃ T a q b, ObsEq
      (run T (input (3*t+1) m)) (regularSection a q b) := by
  obtain ⟨q,b,h⟩ := tail7_regular (64*t+37) m
  refine ⟨firstTime (3*t+1) m+bTime t,64*t+37,q,b,?_⟩
  rw [b_two_return]
  exact h

private theorem branch_E (t m : Nat) :
    ∃ T a q b, ObsEq
      (run T (input (3*t+2) m)) (regularSection a q b) := by
  obtain ⟨q,b,h⟩ := tail13_regular (64*t+49) m
  refine ⟨firstTime (3*t+2) m+eTime t,64*t+49,q,b,?_⟩
  rw [e_two_return]
  exact h

private theorem branch_A (t m : Nat) :
    ∃ T a q b, ObsEq
      (run T (input (3*t) m)) (regularSection a q b) := by
  have hm : m%3=0 ∨ m%3=1 ∨ m%3=2 := by omega
  rcases hm with h0 | h1 | h2
  · have heq : m=3*(m/3) := by omega
    rw [heq]
    refine ⟨firstTime (3*t) (3*(m/3))+aTime t (m/3),
      aUnary t (m/3),0,0,?_⟩
    rw [a_two_return_multiple_three]
    simpa [ObsEq,regularSection,oppairs,run] using
      (source_pad 0 0 0 (regularSection (aUnary t (m/3)) 0 0))
  · have heq : m=3*(m/3)+1 := by omega
    rw [heq]
    refine ⟨firstTime (3*t) (3*(m/3)+1)+aDoubleTime t (m/3),
      aDoubleUnary t (m/3),1,5,?_⟩
    have h := a_two_return_plus_one t (m/3)
    simpa [regularSection,oppairs,List.replicate_succ,List.append_assoc] using h
  · have heq : m=3*(m/3)+2 := by omega
    rw [heq]
    refine ⟨firstTime (3*t) (3*(m/3)+2)+aExtraTime t (m/3),
      aExtraUnary t (m/3),0,0,?_⟩
    have h := a_two_return_plus_two t (m/3)
    simpa [regularSection,oppairs] using h

/-- All prepared E-q0, p2 zero-ended alternating markers reenter
    the regular section language. Proof covers all k,m, with no size bound. -/
theorem all_E_zero_p2_to_regular (k m : Nat) :
    ∃ T a q b, ObsEq
      (run T (input k m)) (regularSection a q b) := by
  have hk : k%3=0 ∨ k%3=1 ∨ k%3=2 := by omega
  rcases hk with h0 | h1 | h2
  · have heq : k=3*(k/3) := by omega
    rw [heq]
    exact branch_A (k/3) m
  · have heq : k=3*(k/3)+1 := by omega
    rw [heq]
    exact branch_B (k/3) m
  · have heq : k=3*(k/3)+2 := by omega
    rw [heq]
    exact branch_E (k/3) m

private theorem oppairs_zero (m : Nat) :
    oppairs m ++ [false] = false :: pairs m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simpa [oppairs,pairs,List.append_assoc] using
      congrArg (fun xs : List Bool => false :: true :: xs) ih

/-- A genuine Z_m marker: m alternating 01 pairs terminated by one zero. -/
def markerZ (m : Nat) : List Bool := oppairs m ++ [false]

private def unpadded (k m : Nat) : List Bool :=
  List.replicate (3*k+2) true ++ false :: ([true,true,false] ++ pairs m)

private theorem marker_shape (k m : Nat) :
    BB6.Agent31PacketSource.packet (3*k+4) 0 2 (markerZ m) =
      init (unpadded k m) := by
  have hn : List.replicate (3*k+4) true =
      true :: true :: List.replicate (3*k+2) true := by
    rw [show 3*k+4=2+(3*k+2) by omega,
      ←List.replicate_append_replicate]
    rfl
  simp [BB6.Agent31PacketSource.packet,BB6.Agent31PacketSource.word,
    markerZ,oppairs_zero,hn,init,unpadded,oppairs,List.append_assoc]

private theorem marker_pad_shape (k m : Nat) :
    init (unpadded k m ++ [false]) = input k m := by
  simp [unpadded,input,List.append_assoc]

/-- Main terminal result for the original six-state machine, from the
    physically authentic packet with one zero-ended marker of any depth.
    All k,m are universally quantified and every class enters a regular L. -/
theorem all_E_zero_p2_marker_regular (k m : Nat) :
    ∃ T a q b, ObsEq
      (run T (BB6.Agent31PacketSource.packet (3*k+4) 0 2 (markerZ m)))
      (regularSection a q b) := by
  obtain ⟨T,a,q,b,h⟩ := all_E_zero_p2_to_regular k m
  refine ⟨T,a,q,b,?_⟩
  have hp := source_init_pad T 1 (unpadded k m)
  change ObsEq (run T (init (unpadded k m)))
      (run T (init (unpadded k m ++ [false]))) at hp
  rw [←marker_shape,marker_pad_shape] at hp
  exact cfgEq_trans hp h

#print axioms all_E_zero_p2_marker_regular
#print axioms all_E_zero_p2_to_regular
end BB6.Agent36EZeroZTwoAll
