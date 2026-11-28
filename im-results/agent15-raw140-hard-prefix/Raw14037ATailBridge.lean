import Raw14037Counter
import Raw140Framed

namespace Raw14037ATailBridge

open BB6BlockFAR Raw140Orbit Raw140Extra Raw14037Counter
open Raw140Double (Reach)

set_option maxRecDepth 100000
set_option maxHeartbeats 0
attribute [local irreducible] boundary run

/--
A framed, finite certificate for the exceptional A-tail emitted by the
Raw37 one-triplet terminal.  The open left suffix is deliberately not
included in the computed prefix; the execution does not inspect it.
-/
def t11511Valid : Prop :=
  Raw140Framed.execute base true false 943
    ⟨3, true,
      [S 6, S 2] ++ U6 15 ++ [S 7] ++ U3 70,
      [S 1, S 1, S 5, S 1, S 1]⟩ =
    some (2629,
      ⟨3, true,
        [S 6, S 2] ++ U6 25 ++ [S 7] ++ U3 65,
        [S 3, S 1]⟩)

theorem t11511_certificate : t11511Valid := by
  decide +kernel

/--
The Raw37 A-tail 11511 converts to the C-tail 31 counter language.
This is the exact parameter instance used after
Raw14037SixBank.advance and Raw14037Terminal.one:
  G(15, 3^70 ++ X, 11511) -> G(25, 3^65 ++ X, 31).
The proof is framed over an arbitrary untouched left suffix X.
-/
theorem t11511_to_c31 (X : List Sym) :
    Reach base
      (G 15 (U3 70 ++ X) [S 1, S 1, S 5, S 1, S 1])
      (G 25 (U3 65 ++ X) [S 3, S 1]) := by
  have h := Raw140Framed.execute_sound base true false 943 2629
    ⟨3, true,
      [S 6, S 2] ++ U6 15 ++ [S 7] ++ U3 70,
      [S 1, S 1, S 5, S 1, S 1]⟩
    ⟨3, true,
      [S 6, S 2] ++ U6 25 ++ [S 7] ++ U3 65,
      [S 3, S 1]⟩
    X [] t11511_certificate
  simpa [G, boundary, U3, U6] using h

#print axioms t11511_to_c31

end Raw14037ATailBridge
