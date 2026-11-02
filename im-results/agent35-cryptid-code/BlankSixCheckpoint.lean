import Lean.Elab.Tactic.Omega
import BlankBeyond
import ESixBlank

set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
namespace CryptidBoundary

/-- Exact symbolic equivalence between a long F-on-zero unary-plus-word
    output and the original raw F-section initializer. -/
theorem finish_packet_init (n : Nat) (ys : List Bool) :
    (⟨[], false, List.replicate (n+2) true ++ ys, 5⟩ : Cfg) =
      init (List.replicate n true ++ ys) := by
  unfold init
  rw [show n+2=2+n by omega]
  rw [←List.replicate_append_replicate]
  rfl

/-- The fourth genuine E boundary returns after 153,499,683,790,798
    primitive raw transitions, without inserting a fictitious trailing zero. -/
theorem blank153499683790798 :
    run 153499683790798 blank =
      init (List.replicate 26524319 true ++ packetSixBlank) := by
  have ht :
    153499683790798 =
      21585935003077 +
        (12*3315539*3315539+49*3315539+58) := by decide
  rw [ht, run_add, blank21585935003077]
  have h := full_E_six_blank 3315539
  have hs : 8*3315539+9=26524319+2 := by omega
  rw [hs] at h
  have he := finish_packet_init 26524319 packetSixBlank
  simpa only [Nat.reduceMul, Nat.reduceAdd] using h.trans he

#print axioms finish_packet_init
#print axioms blank153499683790798
end CryptidBoundary
