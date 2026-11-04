import BB429Mod8
import Lean.Elab.Tactic.Omega
namespace BB429Depth4
/-!
Four finite inverse layers for the terminal residue (u mod 32, w mod 64) = (5,9).
All layers have universal one-step proofs against the exact BB429 next map;
all reachable states from (0,0) avoid every layer.
-/
def B1 (u w : Nat) : Prop :=
  (u%32=6 ∧ w%64=62) ∨
  (u%32=22 ∧ w%64=30) ∨
  (u%32=14 ∧ w%64=46) ∨
  (u%32=30 ∧ w%64=14) ∨
  (u%32=2 ∧ w%64=6) ∨
  (u%32=18 ∧ w%64=38) ∨
  (u%32=10 ∧ w%64=54) ∨
  (u%32=26 ∧ w%64=22)
def B2 (u w : Nat) : Prop :=
  (u%32=15 ∧ w%64=47) ∨
  (u%32=31 ∧ w%64=15) ∨
  (u%32=7 ∧ w%64=63) ∨
  (u%32=23 ∧ w%64=31)
def B3 (u w : Nat) : Prop :=
  (u%32=1 ∧ w%64=14) ∨
  (u%32=17 ∧ w%64=46)
def B4 (u w : Nat) : Prop :=
  (u%32=5 ∧ w%64=9)

set_option maxHeartbeats 4000000 in
theorem safe1 (u w a b : Nat) (h : BB429Mod8.Allowed u w)
    (hs : BB429.next (u,w) = some (a,b)) : ¬B1 a b := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [BB429Mod8.Allowed, B1, Prod.mk.injEq, Option.some.injEq]
  all_goals omega

set_option maxHeartbeats 4000000 in
theorem safe2 (u w a b : Nat) (h : BB429Mod8.Allowed u w) (h1 : ¬B1 u w)
    (hs : BB429.next (u,w) = some (a,b)) : ¬B2 a b := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [BB429Mod8.Allowed, B2, B1, Prod.mk.injEq, Option.some.injEq]
  all_goals omega

set_option maxHeartbeats 4000000 in
theorem safe3 (u w a b : Nat) (h : BB429Mod8.Allowed u w) (h2 : ¬B2 u w)
    (hs : BB429.next (u,w) = some (a,b)) : ¬B3 a b := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [BB429Mod8.Allowed, B3, B2, Prod.mk.injEq, Option.some.injEq]
  all_goals omega

set_option maxHeartbeats 4000000 in
theorem safe4 (u w a b : Nat) (h : BB429Mod8.Allowed u w) (h3 : ¬B3 u w)
    (hs : BB429.next (u,w) = some (a,b)) : ¬B4 a b := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [BB429Mod8.Allowed, B4, B3, Prod.mk.injEq, Option.some.injEq]
  all_goals omega

def Inv (u w : Nat) : Prop :=
  BB429Mod8.Allowed u w ∧ ¬B1 u w ∧ ¬B2 u w ∧ ¬B3 u w ∧ ¬B4 u w

theorem initial_inv : Inv 0 0 := by
  simp [Inv, BB429Mod8.Allowed, B1, B2, B3, B4]

theorem inv_step (u w a b : Nat) (h : Inv u w)
    (hs : BB429.next (u,w) = some (a,b)) : Inv a b := by
  rcases h with ⟨ha,h1,h2,h3,h4⟩
  exact ⟨BB429Mod8.allowed_step u w a b ha hs,
    safe1 u w a b ha hs,
    safe2 u w a b ha h1 hs,
    safe3 u w a b ha h2 hs,
    safe4 u w a b ha h3 hs⟩

theorem all_runs (n u w : Nat)
    (h : BB429.run n (0,0)=some (u,w)) : Inv u w := by
  induction n generalizing u w with
  | zero =>
    simp only [BB429.run,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    exact initial_inv
  | succ n ih =>
    simp only [BB429.run] at h
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at h
    | some s =>
      obtain ⟨a,b⟩ := s
      simp only [hp,Option.bind_some] at h
      exact inv_step a b u w (ih a b hp) h

theorem blank_no_5_9 (n u w : Nat)
    (h : BB429.run n (0,0)=some (u,w)) :
    ¬(u%32=5 ∧ w%64=9) := by
  have hh := (all_runs n u w h).2.2.2.2
  exact hh

theorem blank_halt_u_not_5 (n u w : Nat)
    (h : BB429.run n (0,0)=some (u,w))
    (hn : BB429.next (u,w)=none) : u%32≠5 := by
  have he : w+1=2*u := by
    simp only [BB429.next] at hn
    repeat' (split at hn <;> try cases hn)
    omega
  have hb := blank_no_5_9 n u w h
  omega

#print axioms safe1
#print axioms safe2
#print axioms safe3
#print axioms safe4
#print axioms blank_halt_u_not_5
end BB429Depth4
