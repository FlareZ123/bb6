import BB429Mod8
import Lean.Elab.Tactic.Omega

namespace BB429RootEven8

set_option maxHeartbeats 15000000
set_option maxRecDepth 16000

/--
A stronger exact *one-step* invariant: if the previous state satisfies
the known 17-cell BB429Mod8.Allowed invariant, any positive even successor
has the second counter 2 modulo 8 (not merely modulo 4).
-/
theorem incoming_positive_even_eight (u w a b : Nat)
    (h : BB429Mod8.Allowed u w)
    (hs : BB429.next (u,w)=some (a,b))
    (ha : 0<a) (he : a%2=0) : b%8=2 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [BB429Mod8.Allowed, Prod.mk.injEq, Option.some.injEq]
  all_goals omega

/-- All genuinely blank-root reachable positive even counters obey w%8=2. -/
theorem rooted_positive_even_eight (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (ha : 0<a) (he : a%2=0) : b%8=2 := by
  cases n with
  | zero =>
    simp [BB429.run] at hr
    omega
  | succ n =>
    simp only [BB429.run] at hr
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp, Option.bind_some] at hr
      exact incoming_positive_even_eight p.1 p.2 a b
        (BB429Mod8.all_blank_returns_allowed n p.1 p.2 hp)
        hr ha he

#print axioms incoming_positive_even_eight
#print axioms rooted_positive_even_eight

end BB429RootEven8
