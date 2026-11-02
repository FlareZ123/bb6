import FreshRayGlider
import TurnaroundRay
set_option maxRecDepth 8192

namespace BB6Coverage

inductive GliderKind where
  | threeRight | threeLeft | fourRight | fourLeft | turnRight | turnLeft
  deriving DecidableEq, Repr

structure GliderSpec where
  kind : GliderKind
  b : Fin 6
  c : Fin 6
  u : Bool
  v : Bool
  z : Bool
  deriving Repr

def gliderSpecs : List GliderSpec :=
  ([.threeRight, .threeLeft, .fourRight, .fourLeft, .turnRight, .turnLeft] : List GliderKind).flatMap fun kind =>
    (List.finRange 6).flatMap fun b =>
      (List.finRange 6).flatMap fun c =>
        ([false,true] : List Bool).flatMap fun u =>
          ([false,true] : List Bool).flatMap fun v =>
            ([false,true] : List Bool).map fun z =>
              ⟨kind,b,c,u,v,z⟩

instance (b c : Fin 6) (u : Bool) (p : PartialMachine) :
    Decidable (PartialThreeGlider b c u p) := by
  unfold PartialThreeGlider
  infer_instance

instance (b c : Fin 6) (u : Bool) (p : PartialMachine) :
    Decidable (PartialLeftThreeGlider b c u p) := by
  unfold PartialLeftThreeGlider
  infer_instance

instance (b c : Fin 6) (u v z : Bool) (p : PartialMachine) :
    Decidable (PartialFourGlider b c u v z p) := by
  unfold PartialFourGlider
  infer_instance

instance (b c : Fin 6) (u v z : Bool) (p : PartialMachine) :
    Decidable (PartialLeftGlider b c u v z p) := by
  unfold PartialLeftGlider
  infer_instance

instance (b c : Fin 6) (v : Bool) (p : PartialMachine) :
    Decidable (PartialTurnaround b c v p) := by
  unfold PartialTurnaround
  infer_instance

instance (b c : Fin 6) (v : Bool) (p : PartialMachine) :
    Decidable (PartialLeftTurnaround b c v p) := by
  unfold PartialLeftTurnaround
  infer_instance

def gliderFits (p : PartialMachine) (s : GliderSpec) : Bool :=
  match s.kind with
  | .threeRight => decide (PartialThreeGlider s.b s.c s.u p)
  | .threeLeft => decide (PartialLeftThreeGlider s.b s.c s.u p)
  | .fourRight => decide (PartialFourGlider s.b s.c s.u s.v s.z p)
  | .fourLeft => decide (PartialLeftGlider s.b s.c s.u s.v s.z p)
  | .turnRight => decide (PartialTurnaround s.b s.c s.v p)
  | .turnLeft => decide (PartialLeftTurnaround s.b s.c s.v p)

/-- Executable finite witness search, with a proof-producing answer. -/
def gliderOracle (p : PartialMachine) : Bool :=
  gliderSpecs.any (gliderFits p)

/-- Every accepted sparse table has a source-level all-time nonhalting leaf. -/
theorem gliderOracle_sound (p : PartialMachine) (B : Nat)
    (h : gliderOracle p = true) : Cover (DecidedBelow B) p := by
  obtain ⟨s, _, hs⟩ := List.any_eq_true.mp h
  cases hk : s.kind with
  | threeRight =>
    have hh : PartialThreeGlider s.b s.c s.u p := by
      have hd : decide (PartialThreeGlider s.b s.c s.u p) = true := by
        simpa [gliderFits,hk] using hs
      exact of_decide_eq_true hd
    exact partial_three_glider_cover s.b s.c s.u p B hh
  | threeLeft =>
    have hh : PartialLeftThreeGlider s.b s.c s.u p := by
      have hd : decide (PartialLeftThreeGlider s.b s.c s.u p) = true := by
        simpa [gliderFits,hk] using hs
      exact of_decide_eq_true hd
    exact partial_left_three_glider_cover s.b s.c s.u p B hh
  | fourRight =>
    have hh : PartialFourGlider s.b s.c s.u s.v s.z p := by
      have hd : decide (PartialFourGlider s.b s.c s.u s.v s.z p) = true := by
        simpa [gliderFits,hk] using hs
      exact of_decide_eq_true hd
    exact partial_glider_cover s.b s.c s.u s.v s.z p B hh
  | fourLeft =>
    have hh : PartialLeftGlider s.b s.c s.u s.v s.z p := by
      have hd : decide (PartialLeftGlider s.b s.c s.u s.v s.z p) = true := by
        simpa [gliderFits,hk] using hs
      exact of_decide_eq_true hd
    exact partial_left_glider_cover s.b s.c s.u s.v s.z p B hh

  | turnRight =>
    have hh : PartialTurnaround s.b s.c s.v p := by
      have hd : decide (PartialTurnaround s.b s.c s.v p) = true := by
        simpa [gliderFits,hk] using hs
      exact of_decide_eq_true hd
    exact partial_turnaround_cover s.b s.c s.v p B hh
  | turnLeft =>
    have hh : PartialLeftTurnaround s.b s.c s.v p := by
      have hd : decide (PartialLeftTurnaround s.b s.c s.v p) = true := by
        simpa [gliderFits,hk] using hs
      exact of_decide_eq_true hd
    exact partial_left_turnaround_cover s.b s.c s.v p B hh

theorem oracle_three_example : gliderOracle threeGliderExample = true := by decide
theorem oracle_four_example : gliderOracle gliderExample = true := by decide
theorem oracle_turnaround_example : gliderOracle turnaroundExample = true := by decide
theorem oracle_four_degenerate_example : gliderOracle fourDegenerateExample = true := by decide

theorem oracle_three_leaf (B : Nat) : Cover (DecidedBelow B) threeGliderExample :=
  gliderOracle_sound threeGliderExample B oracle_three_example

theorem oracle_four_degenerate_leaf (B : Nat) :
    Cover (DecidedBelow B) fourDegenerateExample :=
  gliderOracle_sound fourDegenerateExample B oracle_four_degenerate_example

theorem oracle_turnaround_leaf (B : Nat) : Cover (DecidedBelow B) turnaroundExample :=
  gliderOracle_sound turnaroundExample B oracle_turnaround_example

#print axioms oracle_turnaround_leaf
#print axioms gliderOracle_sound
#print axioms oracle_three_leaf
#print axioms oracle_four_degenerate_leaf

end BB6Coverage
