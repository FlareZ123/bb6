import Lean.Elab.Tactic.Omega
import ThirdTailPositive
import PacketSource

set_option maxHeartbeats 8000000
namespace BB6.Agent2ThirdTailSecondBE
open CryptidBoundary BB6.Agent2ThirdTailPositive

private theorem b_input_shape (t q : Nat) :
    packetTarget (3*t) q =
      init (List.replicate (3*(8*t+1)) true ++
        (false::(List.replicate (2*q+2) true ++
          (false::List.replicate 14 true)))) := by
  have hn : 8*(3*t)+5 = 2+3*(8*t+1) := by omega
  simp only [packetTarget, init]
  apply congrArg (fun xs : List Bool => (⟨[],false,xs,5⟩ : Cfg))
  rw [hn, ← List.replicate_append_replicate]
  simp [List.append_assoc]

/-- The B successor of the positive-q packet is an exact source return to L. -/
theorem b_next (t q : Nat) :
    run (768*t*t+584*t+101) (packetTarget (3*t) q) =
    (⟨[],false,List.replicate (64*t+19+2*q) true ++
      (false::List.replicate 14 true),5⟩ : Cfg) := by
  have ht : 768*t*t+584*t+101 =
      12*(8*t+1)*(8*t+1)+49*(8*t+1)+40 := by grind
  rw [ht,b_input_shape,full_B]
  have hn : 8*(8*t+1)+9+(2*q+2)=64*t+19+2*q := by omega
  simp only [← List.append_assoc]
  rw [List.replicate_append_replicate]
  rw [hn]

private theorem e_input_shape (t q : Nat) :
    packetTarget (3*t+1) (q+1) =
    init (List.replicate (3*(8*t+3)+2) true ++
      false::(pairs 0 ++ ([true,true,true] ++
        (List.replicate (2*q+1) true ++
          (false::List.replicate 14 true))))) := by
  have hn : 8*(3*t+1)+5 = 2+(3*(8*t+3)+2) := by omega
  simp only [packetTarget,init,pairs]
  apply congrArg (fun xs : List Bool => (⟨[],false,xs,5⟩ : Cfg))
  rw [hn, ← List.replicate_append_replicate]
  have hp : 2*(q+1)+2 = 3+(2*q+1) := by omega
  rw [hp]
  have h3 : List.replicate (3+(2*q+1)) true =
      [true,true,true] ++ List.replicate (2*q+1) true := by
    rw [← List.replicate_append_replicate]
    rfl
  rw [h3]
  simp [List.append_assoc]

/-- The E successor remains in the explicit packet grammar. -/
theorem e_next (t q : Nat) :
    run (768*t*t+968*t+313)
      (packetTarget (3*t+1) (q+1)) =
    (⟨[],false,List.replicate (64*t+33) true ++
      (oppairs 2 ++ (false::(List.replicate (2*q+1) true ++
        (false::List.replicate 14 true)))),5⟩ : Cfg) := by
  have ht : 768*t*t+968*t+313 =
      12*(8*t+3)*(8*t+3)+49*(8*t+3)+58+6*0 := by grind
  rw [ht,e_input_shape,full_E_triple_pairs]
  have hn : 8*(8*t+3)+9 = 64*t+33 := by omega
  rw [hn]

#print axioms b_next
#print axioms e_next
end BB6.Agent2ThirdTailSecondBE
