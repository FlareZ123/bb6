import BB429Mod8
import Lean.Elab.Tactic.Omega
namespace BB429Thirteen

set_option maxHeartbeats 3000000 in
theorem no_5_38_after_step (u w a b : Nat)
    (h : BB429Mod8.Allowed u w)
    (hs : BB429.next (u,w)=some (a,b)) :
    a%32=5 → b%64≠38 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [BB429Mod8.Allowed, Prod.mk.injEq, Option.some.injEq]
  all_goals omega

set_option maxHeartbeats 3000000 in
theorem no_21_6_after_step (u w a b : Nat)
    (h : BB429Mod8.Allowed u w)
    (hs : BB429.next (u,w)=some (a,b)) :
    a%32=21 → b%64≠6 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [BB429Mod8.Allowed, Prod.mk.injEq, Option.some.injEq]
  all_goals omega

set_option maxHeartbeats 3000000 in
theorem no_13_25_after_step (u w a b : Nat)
    (h5 : u%32=5 → w%64≠38)
    (h21 : u%32=21 → w%64≠6)
    (hs : BB429.next (u,w)=some (a,b)) :
    a%32=13 → b%64≠25 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

def Inv (u w : Nat) : Prop :=
  BB429Mod8.Allowed u w ∧
  (u%32=5 → w%64≠38) ∧
  (u%32=21 → w%64≠6) ∧
  (u%32=13 → w%64≠25)

theorem inv_seed : Inv 0 0 := by
  simp [Inv, BB429Mod8.Allowed]

theorem inv_step (u w a b : Nat) (h : Inv u w)
    (hs : BB429.next (u,w)=some (a,b)) : Inv a b := by
  rcases h with ⟨ha,h5,h21,h13⟩
  exact ⟨BB429Mod8.allowed_step u w a b ha hs,
    no_5_38_after_step u w a b ha hs,
    no_21_6_after_step u w a b ha hs,
    no_13_25_after_step u w a b h5 h21 hs⟩

theorem blank_inv (n u w : Nat)
    (h : BB429.run n (0,0)=some (u,w)) : Inv u w := by
  induction n generalizing u w with
  | zero =>
    simp only [BB429.run,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    exact inv_seed
  | succ n ih =>
    simp only [BB429.run] at h
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at h
    | some s =>
      obtain ⟨a,b⟩ := s
      simp only [hp,Option.bind_some] at h
      exact inv_step a b u w (ih a b hp) h

theorem blank_halt_u_not_13 (n u w : Nat)
    (h : BB429.run n (0,0)=some (u,w))
    (hn : BB429.next (u,w)=none) : u%32≠13 := by
  have hl : w+1=2*u := by
    simp only [BB429.next] at hn
    repeat' (split at hn <;> try cases hn)
    omega
  have h13 := (blank_inv n u w h).2.2.2
  omega

#print axioms no_13_25_after_step
#print axioms blank_halt_u_not_13
end BB429Thirteen
