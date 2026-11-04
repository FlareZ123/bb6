import BB429Rank
import Lean.Elab.Tactic.Omega
namespace BB429LowOddMod8
set_option maxHeartbeats 10000000

/-- For every genuinely reachable positive even counter, the second counter is 2 mod 4. -/
theorem incoming_even_parity (x y a b : Nat)
    (hs : BB429.next (x,y) = some (a,b)) (ha : 0<a) (he : a%2=0) :
    b%4=2 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

theorem rooted_even_parity (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (ha : 0<a) (he : a%2=0) : b%4=2 := by
  cases n with
  | zero => simp [BB429.run] at hr; omega
  | succ n =>
    simp only [BB429.run] at hr
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp, Option.bind_some] at hr
      exact incoming_even_parity p.1 p.2 a b hr ha he

/-- Any odd >= 13 target entered from an admissible genuine root parent
    is either a first-branch output, or has second counter 2 modulo 8. -/
theorem admissible_odd_predecessor (x y a b : Nat)
    (hs : BB429.next (x,y) = some (a,b))
    (ha : a%2=1) (hlarge : 13≤a)
    (heven : 0<x → x%2=0 → y%4=2) :
    (a=2*x+3 ∧ y=b+a) ∨ b%8=2 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

/-- First counter 1 has no incoming transition from any valid accelerated state. -/
theorem no_parent_one (x y b : Nat) :
    BB429.next (x,y) ≠ some (1,b) := by
  intro hs
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

/-- First counter 5, if encountered, has unique predecessor with first counter 1. -/
theorem five_has_only_one (x y b : Nat)
    (hs : BB429.next (x,y)=some (5,b)) : x=1 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

/-- No blank-root visit can have first counter 1. -/
theorem root_ne_one (n b : Nat) :
    BB429.run n (0,0) ≠ some (1,b) := by
  intro h
  cases n with
  | zero => simp [BB429.run] at h
  | succ n =>
    simp only [BB429.run] at h
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at h
    | some p =>
      simp only [hp,Option.bind_some] at h
      exact no_parent_one p.1 p.2 b h

/-- No blank-root visit can have first counter 5. -/
theorem root_ne_five (n b : Nat) :
    BB429.run n (0,0) ≠ some (5,b) := by
  intro h
  cases n with
  | zero => simp [BB429.run] at h
  | succ n =>
    simp only [BB429.run] at h
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at h
    | some p =>
      simp only [hp,Option.bind_some] at h
      have h1 := five_has_only_one p.1 p.2 b h
      have hh : BB429.run n (0,0)=some (1,p.2) := by
        have hpe : p=(1,p.2) := Prod.ext h1 rfl
        rw [hpe] at hp
        exact hp
      exact root_ne_one n p.2 hh

/-- True rooted entry at 13 forces second counter 2 modulo 8. -/
theorem rooted_thirteen (n w : Nat)
    (hr : BB429.run n (0,0)=some (13,w)) : w%8=2 := by
  cases n with
  | zero => simp [BB429.run] at hr
  | succ n =>
    simp only [BB429.run] at hr
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp,Option.bind_some] at hr
      have h := admissible_odd_predecessor p.1 p.2 13 w hr (by decide) (by decide)
        (fun hx he => rooted_even_parity n p.1 p.2 hp hx he)
      rcases h with ⟨ha,hy⟩ | hw
      · have h5 : BB429.run n (0,0) = some (5,p.2) := by
          have hpe : p=(5,p.2) := Prod.ext (by omega) rfl
          rw [hpe] at hp
          exact hp
        exact False.elim ((root_ne_five n p.2) h5)
      · exact hw

/-- True rooted entry at 29 forces second counter in {2,5} modulo 8. -/
theorem rooted_twenty_nine (n w : Nat)
    (hr : BB429.run n (0,0)=some (29,w)) : w%8=2 ∨ w%8=5 := by
  cases n with
  | zero => simp [BB429.run] at hr
  | succ n =>
    simp only [BB429.run] at hr
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp,Option.bind_some] at hr
      have h := admissible_odd_predecessor p.1 p.2 29 w hr (by decide) (by decide)
        (fun hx he => rooted_even_parity n p.1 p.2 hp hx he)
      rcases h with ⟨ha,hy⟩ | hw
      · have h13 : BB429.run n (0,0)=some (13,w+29) := by
          have hpe : p=(13,w+29) := Prod.ext (by omega) (by omega)
          rw [hpe] at hp
          exact hp
        have hm := rooted_thirteen n (w+29) h13
        omega
      · exact Or.inl hw

/-- True blank-reachable first counter 61 has only three second-counter residues. -/
theorem rooted_sixty_one (n w : Nat)
    (hr : BB429.run n (0,0)=some (61,w)) :
    w%8=0 ∨ w%8=2 ∨ w%8=5 := by
  cases n with
  | zero => simp [BB429.run] at hr
  | succ n =>
    simp only [BB429.run] at hr
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp,Option.bind_some] at hr
      have h := admissible_odd_predecessor p.1 p.2 61 w hr (by decide) (by decide)
        (fun hx he => rooted_even_parity n p.1 p.2 hp hx he)
      rcases h with ⟨ha,hy⟩ | hw
      · have h29 : BB429.run n (0,0)=some (29,w+61) := by
          have hpe : p=(29,w+61) := Prod.ext (by omega) (by omega)
          rw [hpe] at hp
          exact hp
        have hm := rooted_twenty_nine n (w+61) h29
        omega
      · exact Or.inr (Or.inl hw)

#print axioms admissible_odd_predecessor
#print axioms rooted_sixty_one
end BB429LowOddMod8
