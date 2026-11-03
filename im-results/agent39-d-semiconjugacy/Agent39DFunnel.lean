import Std

namespace BB6.Agent39

/-!
General conditional theorem composing two previously source-certified D0
F/0 returns. The parameters hB, hA, hAbsorb are the exact original-machine
obligations. They are hypotheses here, not silently re-proved source imports.
-/
def Right (n : Nat) (suffix : List Bool) : List Bool :=
  List.replicate n true ++ suffix

theorem absorb_two (n : Nat) (suffix : List Bool) :
    Right n (true::true::suffix) = Right (n+2) suffix := by
  calc
    Right n (true::true::suffix) =
        (List.replicate n true ++ List.replicate 2 true) ++ suffix := by
          simp [Right, List.replicate_succ, List.append_assoc]
    _ = Right (n+2) suffix := by
      change (List.replicate n true ++ List.replicate 2 true) ++ suffix =
        List.replicate (n+2) true ++ suffix
      rw [List.replicate_append_replicate]

def TimeB (k : Nat) : Nat := 12*k*k+49*k+40

def TimeA (k : Nat) : Nat := 12*k*k+49*k+44

theorem time_difference_four (k : Nat) : TimeA k = TimeB k+4 := by
  simp [TimeA,TimeB]

variable {Cfg : Type} (run : Nat → Cfg → Cfg)
  (I : Nat → List Bool → Cfg)

/-- Verified base macros: B + A-close return, plus literal unary concatenation. -/
def FunnelHypotheses : Prop :=
  (∀ k ys,
    run (TimeB k) (I (3*k+2) (false::ys)) = I (8*k+9) ys) ∧
  (∀ k ys,
    run (TimeA k) (I (3*k+3) (false::false::ys)) = I (8*k+11) ys) ∧
  (∀ n m ys, I n (List.replicate m true++ys) = I (n+m) ys)

/-- Different physical F-section tapes coalesce exactly, four steps apart. -/
theorem four_step_funnel
    (h : FunnelHypotheses run I) (k : Nat) (ys : List Bool) :
    run (TimeB k) (I (3*k+2) (false::true::true::ys)) =
    run (TimeA k) (I (3*k+3) (false::false::ys)) := by
  rcases h with ⟨hb,ha,hn⟩
  rw [hb k (true::true::ys), ha k ys]
  have hcat : I (8*k+9) (true::true::ys) =
              I (8*k+9+2) ys := by
    simpa using hn (8*k+9) 2 ys
  rw [hcat]

/-- All later raw configurations agree with a fixed four-step time offset. -/
theorem four_step_funnel_future
    (h : FunnelHypotheses run I)
    (hadd : ∀ n m s, run (n+m) s = run m (run n s))
    (k : Nat) (ys : List Bool) (j : Nat) :
    run (TimeB k+j) (I (3*k+2) (false::true::true::ys)) =
    run (TimeA k+j) (I (3*k+3) (false::false::ys)) := by
  rw [hadd, hadd]
  exact congrArg (run j) (four_step_funnel run I h k ys)

#print axioms absorb_two
#print axioms time_difference_four
#print axioms four_step_funnel
#print axioms four_step_funnel_future
end BB6.Agent39
