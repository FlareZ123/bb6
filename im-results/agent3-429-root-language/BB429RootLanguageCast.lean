import BB429RootLanguageFatal
import BB429OddExcursion
import Lean.Elab.Tactic.Omega
namespace BB429RootLanguageCast
open Frontier429

def cast (z : Frontier429.Z) : BB429OddExcursion.Zipper :=
  ⟨z.state,z.left,z.cur,z.right⟩

theorem one_cast (z : Frontier429.Z) :
    BB429OddExcursion.one (cast z) = (Frontier429.step z).map cast := by
  rcases z with ⟨s,l,b,r⟩
  cases s with
  | zero => cases b <;> cases l <;> cases r <;> rfl
  | succ s =>
      cases s with
      | zero => cases b <;> cases l <;> cases r <;> rfl
      | succ s =>
          cases s with
          | zero => cases b <;> cases l <;> cases r <;> rfl
          | succ s =>
              cases s with
              | zero => cases b <;> cases l <;> cases r <;> rfl
              | succ s =>
                  cases s with
                  | zero => cases b <;> cases l <;> cases r <;> rfl
                  | succ s =>
                      cases s with
                      | zero => cases b <;> cases l <;> cases r <;> rfl
                      | succ s => cases b <;> rfl

theorem run_cast (n : Nat) (z : Frontier429.Z) :
    BB429OddExcursion.run n (cast z) =
      (Frontier429.run n z).map cast := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
      simp only [BB429OddExcursion.run, Frontier429.run, one_cast]
      cases hz : Frontier429.step z with
      | none => simp [hz]
      | some z' =>
          simp only [hz, Option.map_some, Option.bind_some]
          exact ih z'

theorem original_zipper_fatal (m : Nat) :
    BB429OddExcursion.run (46+8*m)
      ⟨2,[true,false,true,true,true,false] ++ Frontier429.ones2 m ++ [false],false,[]⟩ =
    some ⟨2,Frontier429.pairs (m+2) ++ Frontier429.ones2 3,false,[true]⟩ := by
  have h := run_cast (46+8*m)
    (⟨2,[true,false,true,true,true,false] ++ Frontier429.ones2 m ++ [false],false,[]⟩ : Frontier429.Z)
  rw [BB429RootLanguageFatal.root_grammar_contains_fatal_family] at h
  exact h

#print axioms one_cast
#print axioms run_cast
#print axioms original_zipper_fatal
end BB429RootLanguageCast
