import Agent8RootCancellationBudgetBridge
import RootExclusion
import Lean.Elab.Tactic.Omega

/-!
# A root-mass gap excludes a bounded n=10 far-cancellation strip

The source root run has exact states at steps 39, 40, and 41. Since every
successful blank-root transition increases total mass, the open mass interval
(213720, 347700), except for the unique step-40 state, is unreachable.

The far/far and far/near cancellation bridges place the predecessor within
460 of a 13:1 coordinate ratio at n=10. For scale in [19680,24802], this
forces total mass into that forbidden interval. This is a genuine-root
exclusion for a whole strip, not just for one synthetic witness.
-/ 

namespace BB6.Agent8RootMassGapStripExclusion

open BB6.Agent8RootCancellationBudgetBridge
open BB6.Agent48TerminalBudgetCounterexample
open BB6.Agent49ParitySource

/-- Any state in the 13:1 strip with scale 19680..24802 has mass strictly
inside the root's step-39/40/41 mass gap. -/
theorem far_gap_mass_window (x y E : Nat)
    (hgap : absDiff x (13*y) <= E)
    (hE : E <= 460)
    (hyLo : 19680 <= y) (hyHi : y <= 24802) :
    213720 < x+y /\ x+y < 347700 := by
  have hg := absDiff_le_both x (13*y) E hgap
  constructor <;> omega

/-- Far terminal / far previous-ray cancellation strip: no genuine
blank-root state can satisfy the n=10 bridge hypotheses when the smaller
coordinate lies in [19680,24802]. -/
theorem far_far_n10_root_strip_unreachable
    (t u v x y B e c : Nat)
    (hseen : run t = some (.D u v))
    (hvLo : 19680 <= v) (hvHi : v <= 24802)
    (hB : B <= 145) (he : e <= 306) (hc : c <= 9)
    (hterm : absDiff x (4*y) <= B)
    (hbridgeLo : -(e : Int) <=
      (x : Int)-4*(y : Int)-(c : Int)-((u : Int)-13*(v : Int)))
    (hbridgeHi :
      (x : Int)-4*(y : Int)-(c : Int)-((u : Int)-13*(v : Int)) <= e) :
    False := by
  have ht := absDiff_le_both x (4*y) B hterm
  have hgapLo : -((B+e+c : Nat) : Int) <=
      (u : Int)-13*(v : Int) := by omega
  have hgapHi : (u : Int)-13*(v : Int) <=
      (B+e+c : Nat) := by omega
  have hgap := absDiff_of_int_window u (13*v) (B+e+c)
      hgapLo hgapHi
  have hE : B+e+c <= 460 := by omega
  have hmass := far_gap_mass_window u v (B+e+c) hgap hE hvLo hvHi
  have hroot := root_mass_gap_exclusion t u v hseen
  rcases hroot with hsmall | hmiddle | hlarge
  · omega
  · rcases hmiddle with ⟨hu,hv⟩
    omega
  · omega

/-- Far terminal / near previous-ray cancellation strip: the symmetric
13:1 mass interval is equally unreachable. -/
theorem far_near_n10_root_strip_unreachable
    (t u v x y B e c : Nat)
    (hseen : run t = some (.D u v))
    (huLo : 19680 <= u) (huHi : u <= 24802)
    (hB : B <= 145) (he : e <= 306) (hc : c <= 9)
    (hterm : absDiff x (4*y) <= B)
    (hbridgeLo : -(e : Int) <=
      (x : Int)-4*(y : Int)-(c : Int)-((v : Int)-13*(u : Int)))
    (hbridgeHi :
      (x : Int)-4*(y : Int)-(c : Int)-((v : Int)-13*(u : Int)) <= e) :
    False := by
  have ht := absDiff_le_both x (4*y) B hterm
  have hgapLo : -((B+e+c : Nat) : Int) <=
      (v : Int)-13*(u : Int) := by omega
  have hgapHi : (v : Int)-13*(u : Int) <=
      (B+e+c : Nat) := by omega
  have hgap := absDiff_of_int_window v (13*u) (B+e+c)
      hgapLo hgapHi
  have hE : B+e+c <= 460 := by omega
  have hmass := far_gap_mass_window v u (B+e+c) hgap hE huLo huHi
  have hroot := root_mass_gap_exclusion t u v hseen
  rcases hroot with hsmall | hmiddle | hlarge
  · omega
  · rcases hmiddle with ⟨hu,hv⟩
    omega
  · omega

#print axioms far_gap_mass_window
#print axioms far_far_n10_root_strip_unreachable
#print axioms far_near_n10_root_strip_unreachable

end BB6.Agent8RootMassGapStripExclusion
