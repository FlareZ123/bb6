import BB429Rank
import Lean.Elab.Tactic.Omega
namespace BB429Mod8

def Allowed (u w : Nat) : Prop :=
  (u%8=0 ∧ (w%4=0 ∨ w%4=2)) ∨
  (u%8=1 ∧ (w%4=0 ∨ w%4=1 ∨ w%4=2)) ∨
  (u%8=2 ∧ w%4=2) ∨
  (u%8=3 ∧ (w%4=1 ∨ w%4=2 ∨ w%4=3)) ∨
  (u%8=4 ∧ w%4=2) ∨
  (u%8=5) ∨
  (u%8=6 ∧ w%4=2) ∨
  (u%8=7 ∧ (w%4=2 ∨ w%4=3))

set_option maxHeartbeats 2000000 in
theorem allowed_step (u w a b : Nat)
    (h : Allowed u w) (hs : BB429.next (u,w)=some (a,b)) : Allowed a b := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Allowed, Prod.mk.injEq, Option.some.injEq]
  all_goals omega

theorem initial_allowed : Allowed 0 0 := by
  simp [Allowed]

theorem all_blank_returns_allowed (n : Nat) (a b : Nat)
    (h : BB429.run n (0,0) = some (a,b)) : Allowed a b := by
  induction n generalizing a b with
  | zero =>
    simp only [BB429.run, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    exact initial_allowed
  | succ n ih =>
    simp only [BB429.run] at h
    cases hprev : BB429.run n (0,0) with
    | none => simp [hprev] at h
    | some s =>
      obtain ⟨u,w⟩ := s
      simp only [hprev, Option.bind_some] at h
      exact allowed_step u w a b (ih u w hprev) h

set_option maxHeartbeats 200000 in
theorem no_halting_in_seven_sector (u w : Nat)
    (h : Allowed u w) (hu : u%8=7) : BB429.next (u,w) ≠ none := by
  have hw : w%4=2 ∨ w%4=3 := by unfold Allowed at h; omega
  simp only [BB429.next]
  repeat' (split <;> try simp_all <;> try omega)

set_option maxHeartbeats 2000000 in
theorem halting_u_residue (u w : Nat) (ha : Allowed u w)
    (hn : BB429.next (u,w) = none) :
    u%8=1 ∨ u%8=3 ∨ u%8=5 := by
  simp only [BB429.next] at hn
  repeat' (split at hn <;> try cases hn)
  unfold Allowed at ha
  omega

theorem blank_halting_u_residue (n u w : Nat)
    (h : BB429.run n (0,0)=some (u,w))
    (hn : BB429.next (u,w)=none) : u%8=1 ∨ u%8=3 ∨ u%8=5 :=
  halting_u_residue u w (all_blank_returns_allowed n u w h) hn

theorem blank_never_halts_in_seven_sector (n u w : Nat)
    (h : BB429.run n (0,0) = some (u,w)) (hu : u%8=7) :
    BB429.next (u,w) ≠ none :=
  no_halting_in_seven_sector u w (all_blank_returns_allowed n u w h) hu

#print axioms allowed_step
#print axioms all_blank_returns_allowed
#print axioms blank_never_halts_in_seven_sector
#print axioms blank_halting_u_residue
end BB429Mod8
