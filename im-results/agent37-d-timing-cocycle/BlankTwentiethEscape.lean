import Lean.Elab.Tactic.Omega
import BlankNineteenthRejoin
import ExceptionalE7ThirdReturnEscape

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2TwentiethEscape

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

def seed20 : DRegular.L :=
  ⟨64*BB6.Agent2NineteenthRoot.t19+113,0,0⟩

def terminal2040 : DRegular.L :=
  (DRegular.run 2040 seed20).getD ⟨9,0,0⟩

def t20 : Nat := (terminal2040.a-7)/9

/-- Exact DRegular state and residue after the nineteenth E/A reentry. -/
theorem terminal2040_certificate :
    DRegular.run 2040 seed20 = some ⟨9*t20+7,5,1⟩ ∧
      t20 % 27 = 4 := by decide

theorem terminal2040_exact :
    DRegular.run 2040 seed20 = some ⟨9*t20+7,5,1⟩ :=
  terminal2040_certificate.1

theorem t20_mod27 : t20 % 27 = 4 :=
  terminal2040_certificate.2

def u20 : Nat := t20/3

theorem t20_eq_three_u20_add_one : t20=3*u20+1 := by
  have h := t20_mod27
  dsimp [u20]
  omega

def exception20Time : Nat :=
  BB6.Agent2NineteenthRoot.reentry19Time +
    DRegular.accumulated 2040 seed20

theorem blank_twentieth_exception :
    ObsEq (run exception20Time blank)
      (DRegularSource.sourceSection ⟨9*t20+7,5,1⟩) := by
  apply BB6.Agent25RootChain.extend_regular blank
    BB6.Agent2NineteenthRoot.reentry19Time
    2040 seed20 ⟨9*t20+7,5,1⟩
  · constructor
    · change 64*BB6.Agent2NineteenthRoot.t19+113 ≥ 2
      omega
    · right
      rfl
  · exact terminal2040_exact
  · exact BB6.Agent2NineteenthRoot.blank_nineteenth_reentry

def packet20Time : Nat :=
  BB6.Agent2E7ThirdReturnEscape.totalTime u20 5

def escape20Time : Nat := exception20Time+packet20Time

/-- The twentieth blank-root exception reaches the exact off-L third-return
    packet in the k=3t+1, t=1 mod 3, q=5 family. -/
theorem blank_twentieth_escape :
    ObsEq (run escape20Time blank)
      (BB6.Agent2E7ThirdReturnEscape.sourceEnd u20 5) := by
  have hstart :
      BB6.Agent2E7ThirdReturnEscape.sourceStart u20 5 =
        DRegularSource.sourceSection ⟨9*t20+7,5,1⟩ := by
    unfold BB6.Agent2E7ThirdReturnEscape.sourceStart
    rw [t20_eq_three_u20_add_one]
    congr 1
    omega
  have hpacket :=
    BB6.Agent2E7ThirdReturnEscape.exceptional_EEE_escape u20 5 (by omega)
  rw [hstart] at hpacket
  exact source_chain exception20Time packet20Time blank
    (DRegularSource.sourceSection ⟨9*t20+7,5,1⟩)
    (BB6.Agent2E7ThirdReturnEscape.sourceEnd u20 5)
    blank_twentieth_exception
    (by simpa only [packet20Time] using hpacket)

#print axioms terminal2040_exact
#print axioms t20_mod27
#print axioms blank_twentieth_exception
#print axioms blank_twentieth_escape

end BB6.Agent2TwentiethEscape
