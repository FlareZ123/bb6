import RayMacro
import Lean.Elab.Tactic.Omega
namespace BB6Coverage

/-- The finite blank trace uses only slots already assigned by the sparse machine. -/
def MacroTraceKnown (p : PartialMachine) (w : Machine) (n : Nat) : Prop :=
  ∀ k, k<n → ∀ d, run w k blank=some d →
    p (readSlot d)=some (w (readSlot d))

/-- Any given compatible full machine replays an assigned finite trace exactly. -/
theorem macro_prefix_uniform (p : PartialMachine) (w m : Machine) (n : Nat)
    (hw : compatible p w) (hm : compatible p m)
    (known : MacroTraceKnown p w n) (k : Nat) (hk : k≤n) :
    run m k blank=run w k blank := by
  symm
  apply common_prefix_of_partial_table p w m blank k hw hm
  intro i hi d hd
  exact known i (by omega) d hd

/-- Any verified fresh-ray macro on a finite, fully assigned prefix is a
    sound all-completions sparse nonhalting certificate. -/
theorem sparse_ray_macro_cover (p : PartialMachine) (w : Machine)
    (n delta bound : Nat) (hw : compatible p w)
    (hn : 0<n) (hdelta : 0<delta)
    (htrace : ∃ r, run w n blank=some r ∧ r.state=0 ∧ r.head=(delta:Int) ∧
      ∀ x, (delta:Int)≤x → r.tape x=false)
    (hwindow : ∀ k, k<n → ∀ d, run w k blank=some d → 0≤d.head)
    (known : MacroTraceKnown p w n) :
    Cover (DecidedBelow bound) p := by
  apply Cover.leaf
  intro m hm
  left
  have htrace' : ∃ r, run m n blank=some r ∧ r.state=0 ∧
      r.head=(delta:Int) ∧ ∀ x, (delta:Int)≤x → r.tape x=false := by
    obtain ⟨r,hr,hs,hh,hb⟩ := htrace
    have heq := macro_prefix_uniform p w m n hw hm known n (by omega)
    exact ⟨r,heq.trans hr,hs,hh,hb⟩
  have hwindow' : ∀ k, k<n → ∀ d, run m k blank=some d → 0≤d.head := by
    intro k hk d hd
    have heq := macro_prefix_uniform p w m n hw hm known k (by omega)
    have hwk : run w k blank=some d := by rwa [heq] at hd
    exact hwindow k hk d hwk
  exact fresh_ray_macro_never m n delta hn hdelta htrace' hwindow'

/-- The bounded-window version is convenient for executable finite-tape
    witness generators and automatically inherits the same sparse guarantee. -/
theorem sparse_ray_macro_window_cover (p : PartialMachine) (w : Machine)
    (n delta bound : Nat) (hw : compatible p w)
    (hn : 0<n) (hdelta : 0<delta)
    (htrace : ∃ r, run w n blank=some r ∧ r.state=0 ∧ r.head=(delta:Int))
    (hwindow : ∀ k, k<n → ∀ d, run w k blank=some d →
      0≤d.head ∧ d.head<(delta:Int))
    (known : MacroTraceKnown p w n) :
    Cover (DecidedBelow bound) p := by
  apply Cover.leaf
  intro m hm
  left
  have htrace' : ∃ r, run m n blank=some r ∧ r.state=0 ∧ r.head=(delta:Int) := by
    obtain ⟨r,hr,hs,hh⟩ := htrace
    have heq := macro_prefix_uniform p w m n hw hm known n (by omega)
    exact ⟨r,heq.trans hr,hs,hh⟩
  have hwindow' : ∀ k, k<n → ∀ d, run m k blank=some d →
      0≤d.head ∧ d.head<(delta:Int) := by
    intro k hk d hd
    have heq := macro_prefix_uniform p w m n hw hm known k (by omega)
    have hwk : run w k blank=some d := by rwa [heq] at hd
    exact hwindow k hk d hwk
  exact fresh_ray_macro_never_window m n delta hn hdelta htrace' hwindow'

#print axioms macro_prefix_uniform
#print axioms sparse_ray_macro_cover
#print axioms sparse_ray_macro_window_cover
end BB6Coverage
