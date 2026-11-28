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

/--
Compose the A-tail bridge with the existing 65-triplet C-counter and its
terminal depleter.  This reaches the exact two-bank state that starts the
Raw37 D-phase entry problem.
-/
theorem t11511_to_twoBank :
    Reach base
      (G 15 (U3 70 ++ [S 2]) [S 1, S 1, S 5, S 1, S 1])
      (boundary 1 false []
        (U 2 94 ++ T 11 ++ cword Raw14042CounterLocal.CTail.c32)) := by
  have h0 := t11511_to_c31 [S 2]
  have ht : Raw14042CounterLocal.turn 65 Raw14042CounterLocal.CTail.c31 =
      (10, Raw14042CounterLocal.CTail.c35221) := by
    decide
  have h1 := Raw14037Counter.iterate 65 25 0
    Raw14042CounterLocal.CTail.c31 [S 2]
  have h1' :
      Reach base
        (G 25 (U3 65 ++ [S 2]) [S 3, S 1])
        (G 90 [S 2]
          (T 10 ++ cword Raw14042CounterLocal.CTail.c35221)) := by
    simpa [G, T, cword, ht] using h1
  have h2 := Raw14037Counter.deplete 90 10
    Raw14042CounterLocal.CTail.c35221
  have h2' :
      Reach base
        (G 90 [S 2]
          (T 10 ++ cword Raw14042CounterLocal.CTail.c35221))
        (boundary 1 false []
          (U 2 94 ++ T 11 ++ cword Raw14042CounterLocal.CTail.c32)) := by
    simpa [G, U, T, cword, ccarry, next] using h2
  exact Reach.trans h0 (Reach.trans h1' h2')

#print axioms t11511_to_twoBank

end Raw14037ATailBridge
