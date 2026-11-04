import BB429Mod8
import Lean.Elab.Tactic.Omega
namespace BB429Extra11

set_option maxHeartbeats 2000000 in
theorem step_not_11_1 (u w a b : Nat)
    (h : BB429Mod8.Allowed u w)
    (hs : BB429.next (u,w)=some (a,b)) :
    a%16=11 → b%4≠1 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [BB429Mod8.Allowed, Prod.mk.injEq, Option.some.injEq]
  all_goals omega

theorem blank_not_11_1 (n a b : Nat)
    (h : BB429.run n (0,0)=some (a,b)) :
    a%16=11 → b%4≠1 := by
  cases n with
  | zero => simp [BB429.run] at h; rcases h with ⟨rfl,rfl⟩; omega
  | succ n =>
    simp only [BB429.run] at h
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at h
    | some s =>
      obtain ⟨u,w⟩ := s
      simp only [hp,Option.bind_some] at h
      exact step_not_11_1 u w a b (BB429Mod8.all_blank_returns_allowed n u w hp) h

theorem halt_line_of_none (u w : Nat) (hn : BB429.next (u,w)=none) :
    w+1=2*u := by
  simp only [BB429.next] at hn
  repeat' (split at hn <;> try cases hn)
  omega

theorem blank_halting_mod16 (n u w : Nat)
    (h : BB429.run n (0,0)=some (u,w))
    (hn : BB429.next (u,w)=none) :
    u%16=1 ∨ u%16=3 ∨ u%16=5 ∨ u%16=9 ∨ u%16=13 := by
  have h8 := BB429Mod8.blank_halting_u_residue n u w h hn
  have h11 := blank_not_11_1 n u w h
  have hl := halt_line_of_none u w hn
  omega

#print axioms blank_halting_mod16
#print axioms blank_not_11_1
end BB429Extra11
