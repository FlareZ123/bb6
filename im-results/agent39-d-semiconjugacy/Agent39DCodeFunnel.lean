import Std

namespace BB6.Agent39

/-!
Generalized B/A-code coalescence. Conditional assumptions are verbatim the
original-source conditional returns proved by Agents 31 and 35. No source
module import is made here; this is a Lean-checked abstract composition.
-/
variable {Cfg : Type} (run : Nat → Cfg → Cfg)
  (I : Nat → List Bool → Cfg)
  (code : List Bool → List Bool)
  (weight : List Bool → Nat)
  (cost : Nat → List Bool → Nat)

def BTime (k : Nat) : Nat := 12*k*k + 49*k + 40

def ATime (k : Nat) (word : List Bool) : Nat :=
  12*k*k + 41*k + 32 + cost (4*k+3) word +
  2*(4*k+3+weight word)+6

def Delay (k : Nat) (word : List Bool) : Nat :=
  4 + cost (4*k+3) word + 2*weight word

theorem coded_time_gap (k : Nat) (w : List Bool) :
    ATime weight cost k w = BTime k + Delay weight cost k w := by
  simp [ATime, BTime, Delay]
  omega

def SourceMacroPremises : Prop :=
  (∀ k ys,
    run (BTime k) (I (3*k+2) (false::ys)) = I (8*k+9) ys) ∧
  (∀ k w ys,
    run (ATime weight cost k w)
      (I (3*k+3) (false::(code w ++ false::ys))) =
      I (8*k+11+2*weight w) ys) ∧
  (∀ n m ys, I n (List.replicate m true ++ ys) = I (n+m) ys)

theorem coded_funnel
    (h : SourceMacroPremises run I code weight cost)
    (k : Nat) (w ys : List Bool) :
    run (BTime k)
      (I (3*k+2) (false :: (List.replicate (2*weight w+2) true ++ ys))) =
    run (ATime weight cost k w)
      (I (3*k+3) (false :: (code w ++ false::ys))) := by
  rcases h with ⟨hb,ha,hn⟩
  rw [hb k (List.replicate (2*weight w+2) true ++ ys), ha k w ys]
  rw [hn (8*k+9) (2*weight w+2) ys]
  congr 1
  omega

theorem coded_funnel_future
    (h : SourceMacroPremises run I code weight cost)
    (hadd : ∀ n m s, run (n+m) s = run m (run n s))
    (k : Nat) (w ys : List Bool) (j : Nat) :
    run (BTime k+j)
      (I (3*k+2) (false :: (List.replicate (2*weight w+2) true ++ ys))) =
    run (ATime weight cost k w+j)
      (I (3*k+3) (false :: (code w ++ false::ys))) := by
  rw [hadd, hadd]
  exact congrArg (run j) (coded_funnel run I code weight cost h k w ys)

#print axioms coded_time_gap
#print axioms coded_funnel
#print axioms coded_funnel_future
end BB6.Agent39
