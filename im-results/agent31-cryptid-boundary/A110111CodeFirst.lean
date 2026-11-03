import Lean.Elab.Tactic.Omega
import AExceptionalClosure

namespace BB6.CryptidA110111CodeFirst
open CryptidBoundary
open BB6.CryptidAGenericClosure
open BB6.CryptidE111FirstReturn

set_option maxHeartbeats 8000000

def packet (ys : List Bool) : List Bool :=
  true::true::false::true::true::true::ys

def tail (ys : List Bool) : List Bool :=
  false::true::false::true::false::ys

/-- Arbitrary mixed A-token code followed by the exceptional 110111 cylinder
    has an exact first physical return, in the original six-state raw machine. -/
theorem full_A_code_110111_first_return (k : Nat) (ws ys : List Bool) :
    let m := 4*k+3+CryptidA.wordInc ws
    let elapsed := (12*k*k+41*k+32)+
      (CryptidA.wordCost (4*k+3) ws + (2*m+24))
    let start := init (List.replicate (3*k+1) true ++
      false::(CryptidA.wordCode ws ++ packet ys))
    run elapsed start =
      ⟨[], false, List.replicate (2*m+5) true ++ tail ys, 5⟩ ∧
    ∀ t, 0<t → t<elapsed →
       ¬ IsPhysicalReturn (run t start) := by
  have hend : ∀ (m : Nat) (ys : List Bool), 3 ≤ m →
      run (2*m+24) (CryptidBoundary.aBoundary m (packet ys)) =
        ⟨[], false, List.replicate (2*m+5) true ++ tail ys, 5⟩ := by
    intro m zs hm
    have heq : (m-3)+3 = m := by omega
    have hr := a110111_run (m-3) zs
    rw [heq] at hr
    exact hr
  have hno : ∀ (m : Nat) (ys : List Bool) (t : Nat),
    3 ≤ m → t < 2*m+24 →
      ¬ Physical (run t (CryptidBoundary.aBoundary m (packet ys))) := by
    intro m zs t hm ht
    have heq : (m-3)+3 = m := by omega
    have hs := a110111_first_physical (m-3) zs t
      (by simpa only [heq] using ht)
    simpa [packet, heq] using hs
  exact lift_first_return packet tail (fun m => 2*m+24)
     (fun m => 2*m+5) hend hno k ws ys

#print axioms full_A_code_110111_first_return
end BB6.CryptidA110111CodeFirst
