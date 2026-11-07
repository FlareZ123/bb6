import Lean.Elab.Tactic.Omega
import PacketSource

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

namespace BB6.Agent2BoundaryBZero

open CryptidBoundary BB6.Agent31PacketSource

/-- Complete physical canonical right-tape regular shape. -/
def regularSection (a q b : Nat) : Cfg :=
  ⟨[],false,List.replicate a true ++
    (oppairs q ++ List.replicate b true),5⟩

private theorem one_append (a p : Nat) (ys : List Bool) :
    List.replicate a true ++ (List.replicate p true ++ ys) =
      List.replicate (a+p) true ++ ys := by
  rw [List.append_assoc]
  rw [List.replicate_append_replicate]

/-- The previously unhandled B packet with q=0 has an exact source return
    directly to the regular L(a,1,5) language, for every trailing-one count. -/
theorem b_zero_source (k p : Nat) :
    run (12*k*k+49*k+40)
      (packet (3*k+2) 0 p (false :: List.replicate 6 true)) =
      regularSection (8*k+9+p) 1 5 := by
  let ys := List.replicate p true ++ (false :: List.replicate 6 true)
  have hin : packet (3*k+2) 0 p (false :: List.replicate 6 true) =
      init (List.replicate (3*k) true ++ false :: ys) := by
    have hn : List.replicate (3*k+2) true =
        true :: true :: List.replicate (3*k) true := by
      rw [show 3*k+2=2+3*k by omega,
        ←List.replicate_append_replicate]
      rfl
    simp [packet,word,ys,init,hn]
  have hrun := full_B k ys
  rw [hin, hrun]
  change (⟨[],false,
    List.replicate (8*k+9) true ++
      (List.replicate p true ++
        (false :: List.replicate 6 true)),5⟩ : Cfg) =
        regularSection (8*k+9+p) 1 5
  rw [one_append]
  simp [regularSection,oppairs,List.replicate_succ,List.append_assoc]

/-- For the fixed suffix 0 1^6, an E packet with p=1 is *already* a
    regular L(a,q+2,5) section. Zero raw transitions are required. -/
theorem e_one_regular (a q : Nat) :
    packet a q 1 (false::List.replicate 6 true) =
      regularSection a (q+2) 5 := by
  have hop : oppairs (q+2) = oppairs q ++ [false,true,false,true] := by
    induction q with
    | zero => rfl
    | succ q ih =>
      simpa [oppairs,List.append_assoc] using
        congrArg (fun xs : List Bool => false :: true :: xs) ih
  simp only [packet,word,regularSection,hop]
  simp [List.replicate_succ,List.append_assoc]

#print axioms b_zero_source
#print axioms e_one_regular

end BB6.Agent2BoundaryBZero
