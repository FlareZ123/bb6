import S0CountedDrain
import Rst1PrimeBridge6Source
import Lean.Elab.Tactic.Omega

/-!
# Exact composition through the second S0 drain at the first q4 checkpoint

The first arbitrary-value S0 drain exposes an S1 configuration. The
existing counted Rst1' macro then produces another S1 configuration whose
inner counter is all ones. The second arbitrary-left S0 drain consumes that
counter. This file composes those three existing source theorems without
re-proving the Rst1' setup macro.
-/

namespace BB6Coverage.Agent24FirstQ4Checkpoint

open BB6Coverage
open BB6Coverage.Agent42Q4S0Drain
open BB6Coverage.Agent8Rst1PrimeTail

/-- Initial marker-1 S0 left context, written in the S1 encoder's form. -/
def firstQ4Left0 (L : Nat) : List Bool :=
  markerWord 1 ++ d0 ++ binDec L 0 ++ lh

/-- Left context of the S1 successor after the Rst1' setup macro. -/
def firstQ4Left2 (L A : Nat) : List Bool :=
  markerWord 2 ++ d0 ++
    binDec (L+A+2) (2^(L+A+2)-2^A-1) ++ lh

/-- The exact prefix through the output of the second S0 drain.

This composes:
* the general S0 drain of z, cost drainCost z 0;
* the existing Rst1' macro, cost 97+12*(L+A)+3*z;
* the all-ones S0 drain at width z, cost 6*4^z+42*2^z-12*z-48.
-/
theorem firstQ4Checkpoint_prePostlude
    (L A z : Nat) (hz : z < 2^A) :
    run tm2
      (drainCost z 0 +
        ((97+12*(L+A)+3*z) +
          (6*4^z+42*2^z-12*z-48)))
      (s0Config (firstQ4Left0 L) A z 0 0) =
      some (s0Config (firstQ4Left2 L A) z 0 (2^z-1) (3*z+5)) := by
  have hfirst :=
    s0Config_counted_drain_general (firstQ4Left0 L) A z 0 0 hz
  have hrst :=
    rst1Prime_counted_macro L A z 0
  have hsecond :=
    s0Config_counted_drain_closed
      (firstQ4Left2 L A) z z (3*z+5) (by omega)
  rw [run_append]
  rw [hfirst]
  simp only [Option.bind_some]
  rw [run_append]
  change run tm2 (97+12*(L+A)+3*z)
      (s1Config L 0 1 A 0 z 0) = _ at hrst
  rw [hrst]
  simp only [Option.bind_some]
  have hhead : (0:Int)+5+3*(z:Int) = (3*z+5:Int) := by omega
  simpa [firstQ4Left2, s1Config, hhead] using hsecond

/-- The same initial left context as marker-1/d0/d1pow notation. -/
theorem firstQ4Left0_eq_marker1_d1pow (L : Nat) :
    firstQ4Left0 L = markerWord 1 ++ d0 ++ d1pow L ++ lh := by
  simp [firstQ4Left0, binDec_zero]

#print axioms firstQ4Checkpoint_prePostlude
#print axioms firstQ4Left0_eq_marker1_d1pow

end BB6Coverage.Agent24FirstQ4Checkpoint
