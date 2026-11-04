import BB429Mod8
import Lean.Elab.Tactic.Omega
namespace BB429OneGate

set_option maxHeartbeats 2500000 in
theorem no_15_34_after_step (u w a b : Nat)
    (h : BB429Mod8.Allowed u w)
    (hs : BB429.next (u,w)=some (a,b)) :
    a%32=15 → b%64≠34 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [BB429Mod8.Allowed, Prod.mk.injEq, Option.some.injEq]
  all_goals omega

set_option maxHeartbeats 2500000 in
theorem no_31_2_after_step (u w a b : Nat)
    (h : BB429Mod8.Allowed u w)
    (hs : BB429.next (u,w)=some (a,b)) :
    a%32=31 → b%64≠2 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [BB429Mod8.Allowed, Prod.mk.injEq, Option.some.injEq]
  all_goals omega

set_option maxHeartbeats 2500000 in
theorem no_1_1_after_step (u w a b : Nat)
    (h15 : u%32=15 → w%64≠34)
    (h31 : u%32=31 → w%64≠2)
    (hs : BB429.next (u,w)=some (a,b)) :
    a%32=1 → b%64≠1 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

def Inv (u w : Nat) : Prop :=
  BB429Mod8.Allowed u w ∧
  (u%32=15 → w%64≠34) ∧
  (u%32=31 → w%64≠2) ∧
  (u%32=1 → w%64≠1)

theorem inv_seed : Inv 0 0 := by
  simp [Inv, BB429Mod8.Allowed]

theorem inv_step (u w a b : Nat) (h : Inv u w)
    (hs : BB429.next (u,w)=some (a,b)) : Inv a b := by
  rcases h with ⟨ha,h15,h31,h1⟩
  exact ⟨BB429Mod8.allowed_step u w a b ha hs,
    no_15_34_after_step u w a b ha hs,
    no_31_2_after_step u w a b ha hs,
    no_1_1_after_step u w a b h15 h31 hs⟩

theorem blank_inv (n u w : Nat)
    (h : BB429.run n (0,0)=some (u,w)) : Inv u w := by
  induction n generalizing u w with
  | zero =>
    simp only [BB429.run, Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    exact inv_seed
  | succ n ih =>
    simp only [BB429.run] at h
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at h
    | some s =>
      obtain ⟨a,b⟩ := s
      simp only [hp, Option.bind_some] at h
      exact inv_step a b u w (ih a b hp) h

theorem blank_halt_u_not_1 (n u w : Nat)
    (h : BB429.run n (0,0)=some (u,w))
    (hn : BB429.next (u,w)=none) : u%32≠1 := by
  have hl : w+1=2*u := by
    simp only [BB429.next] at hn
    repeat' (split at hn <;> try cases hn)
    omega
  have h1 := (blank_inv n u w h).2.2.2
  omega

#print axioms blank_halt_u_not_1
#print axioms no_15_34_after_step
#print axioms no_31_2_after_step
#print axioms no_1_1_after_step
end BB429OneGate
