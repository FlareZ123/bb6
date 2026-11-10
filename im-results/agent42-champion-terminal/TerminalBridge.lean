import TerminalLeft
import Frontier
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.TerminalBridge
open TerminalFinish

/-- The same literal twelve rule entries as the original BusyCoq TM63. -/
def tm63 : Machine := fun (q,b) =>
 match q.val,b with
 | 0,false => some ⟨true,true,1⟩
 | 0,true  => none
 | 1,false => some ⟨true,false,2⟩
 | 1,true  => some ⟨false,true,5⟩
 | 2,false => some ⟨true,true,4⟩
 | 2,true  => some ⟨false,false,3⟩
 | 3,false => some ⟨false,false,2⟩
 | 3,true  => some ⟨true,true,1⟩
 | 4,false => some ⟨true,true,0⟩
 | 4,true  => some ⟨true,true,4⟩
 | 5,false => some ⟨true,true,4⟩
 | 5,true  => some ⟨false,true,3⟩
 | _,_ => none

def embed (c : TerminalFinish.Conf) : BB6Coverage.Config :=
  { state := ⟨c.q % 6, Nat.mod_lt c.q (by decide)⟩,
    head := c.h, tape := c.t }

theorem step_valid (c d : TerminalFinish.Conf) (hq : c.q<6)
 (hs : TerminalFinish.step c = some d) : d.q<6 := by
  cases c with
  | mk q h t =>
    change q<6 at hq
    have casesq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
    rcases casesq with hx|hx|hx|hx|hx|hx <;> subst q <;>
      cases hb : t h <;>
      simp [TerminalFinish.step,TerminalFinish.action,hb] at hs <;>
      cases hs <;> simp

theorem step_transport (c : TerminalFinish.Conf) (hq : c.q<6) :
 (TerminalFinish.step c).map embed = BB6Coverage.rawStep tm63 (embed c) := by
  cases c with
  | mk q h t =>
    change q<6 at hq
    have casesq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
    rcases casesq with hx|hx|hx|hx|hx|hx <;> subst q <;>
      cases hb : t h <;>
      simp [TerminalFinish.step,TerminalFinish.action, BB6Coverage.rawStep,
        BB6Coverage.applyMove, tm63, embed,TerminalFinish.set,hb] <;>
      (try (rw [show (3:Fin 6).val = 3 by decide]; simp [BB6Coverage.applyMove,TerminalFinish.set])) <;>
      (try (rw [show (4:Fin 6).val = 4 by decide]; simp [BB6Coverage.applyMove,TerminalFinish.set])) <;>
      (try (rw [show (5:Fin 6).val = 5 by decide]; simp [BB6Coverage.applyMove,TerminalFinish.set])) <;>
      (try (funext x; by_cases hx : x=h <;> simp [TerminalFinish.set,hx]))

theorem run_valid (n : Nat) (c d : TerminalFinish.Conf)
 (hc : c.q<6) (hr : TerminalFinish.run n c = some d) : d.q<6 := by
  induction n generalizing d with
  | zero =>
    simp only [TerminalFinish.run, Option.some.injEq] at hr
    subst d
    exact hc
  | succ n ih =>
    simp only [TerminalFinish.run] at hr
    cases hs : TerminalFinish.run n c with
    | none => simp [hs] at hr
    | some s =>
      have hq := ih s hs
      simp only [hs,Option.bind_some] at hr
      exact step_valid s d hq hr

theorem run_transport (n : Nat) (c : TerminalFinish.Conf) (hc : c.q<6) :
 (TerminalFinish.run n c).map embed = BB6Coverage.run tm63 n (embed c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [TerminalFinish.run, BB6Coverage.run]
    rw [← ih]
    cases hs : TerminalFinish.run n c with
    | none => simp [hs]
    | some s =>
      have hq : s.q<6 := run_valid n c s hc hs
      simp only [hs,Option.bind_some,Option.map_some]
      exact step_transport s hq

/-- The terminal exact-step theorem now uses the unchanged BB6Coverage.run
    semantics from Frontier, not a second copy of the run definition. -/
theorem tm63_terminal_exact (L a b : Nat) (h : Int) :
 ∃ c : BB6Coverage.Config,
    BB6Coverage.run tm63 (59+12*(L+a))
     ⟨3,h,TerminalFinish.literalS1Tape L a b h⟩ = some c ∧
    c.state = 0 ∧ c.head = h+7 ∧ c.tape (h+7) = true := by
 obtain ⟨t,ht,hr⟩ := TerminalFinish.literalS1_terminalExact L a b h
 let c : TerminalFinish.Conf := ⟨3,h,TerminalFinish.literalS1Tape L a b h⟩
 have hs := run_transport (59+12*(L+a)) c (by dsimp [c]; decide)
 dsimp only [c] at hs
 rw [ht] at hs
 refine ⟨embed ⟨0,h+7,t⟩, ?_, ?_, ?_, ?_⟩
 · exact hs.symm
 · rfl
 · rfl
 · exact hr

#print axioms tm63_terminal_exact
end BB6Coverage.TerminalBridge
