import SDisjoint
import Init.Omega
namespace BB6.Agent9SPhysicalPhase
open BB6.Agent9SExp
open BB6.Agent9SDisjoint

/-- Exact q=b+16 representation of the source S-only rule. `none` is T-transfer,
    not a primitive Turing machine halt. -/
def stepS (s : Nat × Nat) : Option (Nat × Nat) :=
  let q := s.1
  let c := s.2
  if q % 3 = 0 then
    if c = 0 then none else some (nextQ q, c-1)
  else if q % 3 = 1 then some (nextQ q, c+4)
  else some (nextQ q, c+6)

def runS (s : Nat × Nat) : Nat → Option (Nat × Nat)
  | 0 => some s
  | n+1 => (runS s n).bind stepS

theorem stepS_q (s t : Nat × Nat) (h : stepS s = some t) :
    t.1 = nextQ s.1 := by
  by_cases h0 : s.1 % 3 = 0
  · by_cases hc : s.2 = 0
    · simp [stepS,h0,hc] at h
    · simp [stepS,h0,hc] at h
      cases h
      rfl
  · by_cases h1 : s.1 % 3 = 1
    · simp [stepS,h0,h1] at h
      cases h
      rfl
    · simp [stepS,h0,h1] at h
      cases h
      rfl

theorem runS_q (s t : Nat × Nat) (n : Nat)
    (h : runS s n = some t) : t.1 = iterQ s.1 n := by
  induction n generalizing t with
  | zero =>
    simp [runS] at h
    subst t
    rfl
  | succ n ih =>
    simp only [runS] at h
    cases hpre : runS s n with
    | none => simp [hpre] at h
    | some p =>
      simp only [hpre, Option.bind_some] at h
      have hq : p.1 = iterQ s.1 n := ih p hpre
      have hz : t.1 = nextQ p.1 := stepS_q p t h
      rw [hz, hq]
      rfl

/-- Surviving rooted S phases cannot share even their q-counter at any epochs. -/
theorem surviving_roots_ne (a b : Nat) (s t : Nat × Nat)
    (hs : runS (17,3) a = some s)
    (ht : runS (141,3) b = some t) : s.1 ≠ t.1 := by
  have h1 : s.1 = iterQ 17 a := runS_q _ _ _ hs
  have h2 : t.1 = iterQ 141 b := runS_q _ _ _ ht
  rw [h1, h2]
  exact roots_ne a b

#print axioms BB6.Agent9SPhysicalPhase.surviving_roots_ne
end BB6.Agent9SPhysicalPhase
