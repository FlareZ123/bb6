import RayMacro
import Lean.Elab.Tactic.Omega
namespace BB6Coverage

def macroExample : Machine := fun s =>
  if s=(0,false) then some ⟨true,true,1⟩
  else if s=(1,false) then some ⟨false,false,2⟩
  else if s=(2,true) then some ⟨false,true,0⟩
  else none

def macroEx1 : Config := applyMove blank ⟨true,true,1⟩
def macroEx2 : Config := applyMove macroEx1 ⟨false,false,2⟩
def macroEx3 : Config := applyMove macroEx2 ⟨false,true,0⟩

example : run macroExample 1 blank=some macroEx1 := by rfl
example : run macroExample 2 blank=some macroEx2 := by rfl
example : run macroExample 3 blank=some macroEx3 := by rfl
example : macroEx3.state=0 := by rfl
example : macroEx3.head=1 := by rfl

private theorem macroEx3_tail : ∀ x:Int, 1≤x → macroEx3.tape x=false := by
  intro x hx
  have hn0 : x≠0 := by omega
  simp [macroEx3,macroEx2,macroEx1,applyMove,blank,hn0]

private theorem macroEx_window : ∀ k, k<3 → ∀ d, run macroExample k blank=some d → 0≤d.head := by
  intro k hk d hd
  have cases : k=0∨k=1∨k=2 := by omega
  rcases cases with h|h|h
  · subst k
    have heq : d=blank := by simpa [run] using hd.symm
    subst d
    simp [blank]
  · subst k
    have heq : d=macroEx1 := Option.some.inj (hd.symm.trans (by rfl))
    subst d
    simp [macroEx1,applyMove,blank]
  · subst k
    have heq : d=macroEx2 := Option.some.inj (hd.symm.trans (by rfl))
    subst d
    simp [macroEx2,macroEx1,applyMove,blank]

/-- Nontrivial three-step head-reversing example instantiates ray pumping. -/
theorem macro_example_never : NeverHalts macroExample := by
  apply fresh_ray_macro_never macroExample 3 1 (by decide) (by decide)
  · refine ⟨macroEx3,?_,?_,?_,?_⟩
    · rfl
    · rfl
    · rfl
    · exact macroEx3_tail
  · exact macroEx_window

#print axioms macro_example_never
end BB6Coverage
