import Lean.Elab.Tactic.Omega
import ExceptionalAGeneral

set_option maxHeartbeats 10000000

namespace BB6.EExceptionalShift
open CryptidBoundary BB6.BoundaryPadding

/-- Canonical regular E boundary, including q+1 alternating pairs,
    represented by EAll's original-machine 1100 first-return theorem. -/
theorem e_input (k q : Nat) :
    DRegularSource.sourceSection ⟨3*k+4,q+1,1⟩ =
      init (List.replicate (3*k+2) true ++
        false :: (pairs q ++ [true,true])) := by
  have hn : (3*k+4)-2=3*k+2 := by omega
  simp only [DRegularSource.sourceSection, init, hn, List.replicate_one]
  rw [List.append_assoc, BB6.Agent25BGeneral.oppairs_last]

theorem e_source (k q : Nat) :
    ObsEq
      (run (BB6.Agent32EAll.duration k q)
        (DRegularSource.sourceSection ⟨3*k+4,q+1,1⟩))
      (BB6.Agent32EAll.output k q []) := by
  rw [e_input]
  exact BB6.Agent32EAll.all_e_double_implicit_blank k q

private theorem plus_replicate (k p c : Nat) (tail : List Bool) :
    List.replicate (8*(k+p)+c) true ++ tail =
      List.replicate (8*p) true ++
        (List.replicate (8*k+c) true ++ tail) := by
  have hn : 8*(k+p)+c = 8*p+(8*k+c) := by omega
  rw [hn, ←List.replicate_append_replicate, List.append_assoc]

/-- The first nonregular E-exception return shifts its ENTIRE physical
    output word by 8p unary ones. The complete packet suffix is fixed,
    including the q=0 packetZero exception. -/
theorem output_shift (k q p : Nat) :
    (BB6.Agent32EAll.output (k+p) q []).r =
      List.replicate (8*p) true ++ (BB6.Agent32EAll.output k q []).r := by
  cases q with
  | zero =>
    simpa [BB6.Agent32EAll.output] using
      (plus_replicate k p 3 BB6.Agent32EZero.packetZero)
  | succ n =>
    simpa [BB6.Agent32EAll.output] using
      (plus_replicate k p 5
        (false :: List.replicate (2*(n+1)+2) true ++
          (false :: List.replicate 6 true)))

private theorem quad (k p c : Nat) :
    12*(k+p)*(k+p)+49*(k+p)+c =
      12*k*k+49*k+c+(24*k+49)*p+12*p*p := by
  have h : p*k=k*p := Nat.mul_comm p k
  simp only [Nat.add_mul,Nat.mul_add,Nat.mul_assoc]
  omega

/-- The exceptional E source first-return time has the SAME universal
    curvature 12p² as all eleven regular rows. -/
theorem duration_shift (k q p : Nat) :
    BB6.Agent32EAll.duration (k+p) q =
      BB6.Agent32EAll.duration k q + (24*k+49)*p +12*p*p := by
  cases q with
  | zero => simpa [BB6.Agent32EAll.duration,Nat.add_assoc] using (quad k p 96)
  | succ n =>
    simpa [BB6.Agent32EAll.duration,Nat.add_assoc] using
      (quad k p (64+4*n))

#print axioms e_source
#print axioms output_shift
#print axioms duration_shift
end BB6.EExceptionalShift
