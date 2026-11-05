import BB429RootEven8
import Lean.Elab.Tactic.Omega
namespace BB429SevenStrong
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000

/-- Any exact source transition entering first-counter residue seven mod eight
    has only second-counter residues two or three mod eight, provided the
    actual parent obeys the true-blank even-counter invariant. -/
theorem incoming_seven_strong (x y a b : Nat)
    (hs : BB429.next (x,y)=some (a,b))
    (ha : a%8=7)
    (hparent : 0<x → x%2=0 → y%8=2) :
    b%8=2 ∨ b%8=3 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

/-- A strengthened genuine blank-root congruence condition, valid at every
    accelerated return time and for all natural counters. -/
theorem rooted_seven_strong (n a b : Nat)
    (hr : BB429.run n (0,0) = some (a,b))
    (ha : a%8=7) : b%8=2 ∨ b%8=3 := by
  cases n with
  | zero =>
    simp [BB429.run] at hr
    omega
  | succ n =>
    simp only [BB429.run] at hr
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp,Option.bind_some] at hr
      exact incoming_seven_strong p.1 p.2 a b hr ha
        (fun hx he => BB429RootEven8.rooted_positive_even_eight n p.1 p.2 hp hx he)

/-- A true-blank parent entering counter 1 modulo 16 has second counter
    restricted to residues 1 or 2 modulo 8. -/
theorem incoming_one_strong (x y a b : Nat)
    (hs : BB429.next (x,y)=some (a,b))
    (ha : a%16=1)
    (heven : 0<x → x%2=0 → y%8=2)
    (hseven : x%8=7 → (y%8=2 ∨ y%8=3)) :
    b%8=1 ∨ b%8=2 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

/-- Strengthening the existing source invariant for all authentic blank
    accelerated returns, without any time cutoff. -/
theorem rooted_one_strong (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (ha : a%16=1) : b%8=1 ∨ b%8=2 := by
  cases n with
  | zero =>
    simp [BB429.run] at hr
    omega
  | succ n =>
    simp only [BB429.run] at hr
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp,Option.bind_some] at hr
      exact incoming_one_strong p.1 p.2 a b hr ha
        (fun hx he => BB429RootEven8.rooted_positive_even_eight n p.1 p.2 hp hx he)
        (fun he => rooted_seven_strong n p.1 p.2 hp he)

/-- Second layer of the authentic low-counter predecessor tower. -/
theorem incoming_five_strong (x y a b : Nat)
    (hs : BB429.next (x,y)=some (a,b))
    (ha : a%32=5)
    (heven : 0<x → x%2=0 → y%8=2)
    (hone : x%16=1 → (y%8=1 ∨ y%8=2)) :
    b%8=2 ∨ b%8=4 ∨ b%8=5 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

theorem rooted_five_strong (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (ha : a%32=5) : b%8=2 ∨ b%8=4 ∨ b%8=5 := by
  cases n with
  | zero =>
    simp [BB429.run] at hr
    omega
  | succ n =>
    simp only [BB429.run] at hr
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp,Option.bind_some] at hr
      exact incoming_five_strong p.1 p.2 a b hr ha
        (fun hx he => BB429RootEven8.rooted_positive_even_eight n p.1 p.2 hp hx he)
        (fun he => rooted_one_strong n p.1 p.2 hp he)

/-- Direct full-cylinder corollary. This previously known exclusion follows
    immediately from the new stronger low-counter section invariant. -/
theorem no_halt_five_mod32 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (hg : b+1=2*a) (ha : a%32=5) : False := by
  have h := rooted_five_strong n a b hr ha
  omega

#print axioms incoming_seven_strong
#print axioms rooted_seven_strong
#print axioms incoming_one_strong
#print axioms rooted_one_strong
#print axioms incoming_five_strong
#print axioms rooted_five_strong
#print axioms no_halt_five_mod32
end BB429SevenStrong
