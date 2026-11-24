import BitCarry
open BB6.Agent28BitCarry
namespace BB6.Agent28ModScreen
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option exponentiation.threshold 20000

def checkCert (p : Nat × Nat) : Bool :=
  let (r,k) := p
  let L := Nat.log2 (r+4+k)+1
  r%2 == 0 && decide (r+4+k < 2^L) && (modRun L r 1 (2^((r+2)/2)) k == 0)

theorem checkCert_sound (p : Nat × Nat) (h : checkCert p=true) :
    p.1%2=0 ∧ listRun p.1 1 [((p.1+2)/2)] p.2=[] := by
  obtain ⟨r,k⟩ := p
  simp [checkCert, Bool.and_eq_true] at h
  exact ⟨h.1.1, empty_of_modRun_zero _ r k h.1.2 (by simpa using h.2)⟩

end BB6.Agent28ModScreen
