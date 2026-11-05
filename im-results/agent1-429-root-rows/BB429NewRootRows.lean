import BB429RootEven8
import Lean.Elab.Tactic.Omega

namespace BB429NewRootRows
set_option maxHeartbeats 15000000
set_option maxRecDepth 16000

theorem incoming_eleven (u w a b : Nat)
    (heven : 0<u → u%2=0 → w%8=2)
    (hs : BB429.next (u,w)=some (a,b))
    (ha : a%16=11) : b%8=2 ∨ b%8=6 ∨ b%8=7 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals (by_cases hu : 0<u <;> by_cases he : u%2=0 <;>
    (try have hw := heven hu he) <;> omega)

theorem rooted_eleven (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (ha : a%16=11) : b%8=2 ∨ b%8=6 ∨ b%8=7 := by
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
      exact incoming_eleven p.1 p.2 a b
        (fun hx he => BB429RootEven8.rooted_positive_even_eight
          n p.1 p.2 hp hx he) hr ha

theorem incoming_nineteen_or_twentyseven (u w a b : Nat)
    (heven : 0<u → u%2=0 → w%8=2)
    (hs : BB429.next (u,w)=some (a,b))
    (ha : a%32=19 ∨ a%32=27) : b%8=2 ∨ b%8=7 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals (by_cases hu : 0<u <;> by_cases he : u%2=0 <;>
    (try have hw := heven hu he) <;> omega)

theorem rooted_nineteen_or_twentyseven (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (ha : a%32=19 ∨ a%32=27) : b%8=2 ∨ b%8=7 := by
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
      exact incoming_nineteen_or_twentyseven p.1 p.2 a b
        (fun hx he => BB429RootEven8.rooted_positive_even_eight
          n p.1 p.2 hp hx he) hr ha

#print axioms rooted_eleven
#print axioms rooted_nineteen_or_twentyseven
end BB429NewRootRows
