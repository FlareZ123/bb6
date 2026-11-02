import STTransferResidues
import STransferTarget
import Init.Omega
namespace BB6.Agent9STransferGate
open BB6.Agent9SExp BB6.Agent9STResidues BB6.Agent9STransfer

/-- Exact original S-transfer q residue test for a halt on the immediately
following high-level T macro. A later T halt is not classified here. -/
theorem transfer_immediate_halt_iff (b c m : Nat)
    (h : sourceSResult b c = .inr m) :
    immediateHalt m ↔
    (b+16)%729=0 ∨ (b+16)%729=81 ∨ (b+16)%729=243 ∨
    (b+16)%729=324 ∨ (b+16)%729=405 ∨
    (b+16)%729=486 ∨ (b+16)%729=567 := by
  have hq := transfer_q b c m h
  have hmod : (b+16)%3=0 := hq.2.1
  have hdiv : m+17=4*((b+16)/3) := by
    have heq := hq.2.2
    unfold nextQ at heq
    simpa only [hmod, ite_true] using heq
  rw [immediate_halt_seven_residues]
  omega

#print axioms BB6.Agent9STransferGate.transfer_immediate_halt_iff
end BB6.Agent9STransferGate
