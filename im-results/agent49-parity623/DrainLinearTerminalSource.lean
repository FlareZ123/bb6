import Agent49DrainLinearLogSource
import Agent8TerminalIntervalSource

/-!
DRAFT: sharper terminal-parent interval obtained by combining the
linear-logarithmic B-drain upper bound and the logarithmic first-counter
loss bound with the existing source one-step terminal gate.

The interval arithmetic has compiled locally with Lean 4.36.0-rc2 against the
exact recursion model and abstract one-step gate inequalities. Full pinned
source-import compilation remains pending.
-/

namespace BB6.Agent49DrainLinearTerminalSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent8DrainFirstSharpSource
open BB6.Agent8DrainSevenSource
open BB6.Agent8BudgetSource
open BB6.Agent49DrainLinearLogSource

/-- A successful drain that is followed by a halting daughter must have
its input first counter within a logarithmic-width interval around d+3b. -/
theorem drainB_terminal_interval_linear (a b d n aa dd : Nat)
    (hs : drainB a b d = some (.D aa dd))
    (hb : b<3^n)
    (he : aa%2=0)
    (hhalt : highLevelNext (.D aa dd) = none) :
    3^((d+3*b)-(a+n)-5) ≤ 2*(a+d+3*b+5*n+2)+5 ∧
    3^(a-d-3*b-5*n-8) ≤ 2*(a+d+3*b+5*n+2)+5 := by
  have hf := drainB_first_le_pow n a b d aa dd hb hs
  have hl := drainB_first_lower_log n a b d aa dd hb hs
  have hd := drainB_d3 b a d aa dd hs
  have hu := drainB_upper_linear_log n a b d aa dd hb hs
  have hg := BB6.Agent49ParitySource.next_none_requires_pow_gap aa dd he hhalt
  have hm : aa+dd ≤ a+d+3*b+5*n+2 := by omega
  constructor
  · have hr : (d+3*b)-(a+n)-5 ≤ dd-aa-5 := by omega
    have hp := Nat.pow_le_pow_right (by omega : 0<3) hr
    omega
  · have hr : (a-d-3*b-5*n-8) ≤ aa-dd-5 := by omega
    have hp := Nat.pow_le_pow_right (by omega : 0<3) hr
    omega

/-- If K dominates the terminal mass by 3^K, a terminal daughter
forces the final drain input balance into the following sharp interval. -/
theorem drainB_terminal_balance_interval (a b d n K aa dd : Nat)
    (hs : drainB a b d = some (.D aa dd))
    (hb : b<3^n)
    (he : aa%2=0)
    (hhalt : highLevelNext (.D aa dd) = none)
    (hK : 2*(a+d+3*b+5*n+2)+5 < 3^K) :
    d+3*b ≤ a+n+K+4 ∧ a ≤ d+3*b+5*n+K+7 := by
  have hi := drainB_terminal_interval_linear a b d n aa dd hs hb he hhalt
  constructor
  · by_cases h : d+3*b ≤ a+n+K+4
    · exact h
    · have hexp : K ≤ (d+3*b)-(a+n)-5 := by omega
      have hp := Nat.pow_le_pow_right (by omega : 0<3) hexp
      omega
  · by_cases h : a ≤ d+3*b+5*n+K+7
    · exact h
    · have hexp : K ≤ a-d-3*b-5*n-8 := by omega
      have hp := Nat.pow_le_pow_right (by omega : 0<3) hexp
      omega

#print axioms drainB_terminal_interval_linear
/-- Even-right first-evaluator plus final-drain terminality confines
the original right-ray balance d-4*a to a logarithmic interval. -/
theorem evenRight_terminal_balance_interval
    (a d n0 n K x b y aa dd : Nat)
    (hRight : a≤d)
    (ha : a<3^n0)
    (hbpos : 0<b)
    (hEval : evalA (d+1-a) a (2*a+5) = some (x,b,y))
    (hDrain : drainB x b y = some (.D aa dd))
    (hb : b<3^n)
    (he : aa%2=0)
    (hhalt : highLevelNext (.D aa dd) = none)
    (hK : 2*(x+y+3*b+5*n+2)+5 < 3^K) :
    4*a≤d+n+K+3 ∧ d≤4*a+5*n+K+11+3*n0 := by
  obtain ⟨r,s,hrs,hrpos,hbs,hfirst,hpot⟩ :=
    evalA_positive_depth n0 (d+1-a) a (2*a+5) x b y ha hbpos hEval
  have hfirstUpper :=
    evalA_first_upper_one (d+1-a) a (2*a+5) x b y hEval
  have hthirdLower :=
    evalA_third_lower (d+1-a) a (2*a+5) x b y hEval
  have hbal :=
    drainB_terminal_balance_interval x b y n K aa dd hDrain hb he hhalt hK
  omega

#print axioms drainB_terminal_balance_interval
#print axioms evenRight_terminal_balance_interval
end BB6.Agent49DrainLinearTerminalSource
