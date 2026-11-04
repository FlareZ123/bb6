import BB429Mod8
import Lean.Elab.Tactic.Omega
import BB429Extra11
namespace BB429Extra19

set_option maxHeartbeats 2500000 in
theorem step_not_8_0 (u w a b : Nat)
    (h : BB429Mod8.Allowed u w)
    (hs : BB429.next (u,w) = some (a,b)) :
    a%16=8 → b%4≠0 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [BB429Mod8.Allowed, Prod.mk.injEq, Option.some.injEq]
  all_goals omega

theorem blank_not_8_0 (n a b : Nat)
    (h : BB429.run n (0,0)=some (a,b)) :
    a%16=8 → b%4≠0 := by
  cases n with
  | zero =>
    simp only [BB429.run, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    omega
  | succ n =>
    simp only [BB429.run] at h
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at h
    | some s =>
      obtain ⟨u,w⟩ := s
      simp only [hp, Option.bind_some] at h
      exact step_not_8_0 u w a b (BB429Mod8.all_blank_returns_allowed n u w hp) h

set_option maxHeartbeats 3000000 in
theorem step_not_19_1 (u w a b : Nat)
    (h : BB429Mod8.Allowed u w)
    (h8 : u%16=8 → w%4≠0)
    (hs : BB429.next (u,w) = some (a,b)) :
    a%32=19 → b%4≠1 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [BB429Mod8.Allowed, Prod.mk.injEq, Option.some.injEq]
  all_goals omega

theorem blank_not_19_1 (n a b : Nat)
    (h : BB429.run n (0,0)=some (a,b)) :
    a%32=19 → b%4≠1 := by
  cases n with
  | zero =>
    simp only [BB429.run, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    omega
  | succ n =>
    simp only [BB429.run] at h
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at h
    | some s =>
      obtain ⟨u,w⟩ := s
      simp only [hp, Option.bind_some] at h
      exact step_not_19_1 u w a b
        (BB429Mod8.all_blank_returns_allowed n u w hp)
        (blank_not_8_0 n u w hp) h

set_option maxHeartbeats 3000000 in
theorem blank_halting_mod32 (n u w : Nat)
    (h : BB429.run n (0,0)=some (u,w))
    (hn : BB429.next (u,w)=none) :
    u%32=1 ∨ u%32=3 ∨ u%32=5 ∨ u%32=9 ∨ u%32=13 ∨
    u%32=17 ∨ u%32=21 ∨ u%32=25 ∨ u%32=29 := by
  have h8 := BB429Mod8.blank_halting_u_residue n u w h hn
  have h11 := BB429Extra11.blank_not_11_1 n u w h
  have h19 := blank_not_19_1 n u w h
  have hl : w+1=2*u := by
    simp only [BB429.next] at hn
    repeat' (split at hn <;> try cases hn)
    omega
  omega

#print axioms step_not_8_0
#print axioms step_not_19_1
#print axioms blank_halting_mod32
end BB429Extra19
