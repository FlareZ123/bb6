import BB429RootEven8
import Lean.Elab.Tactic.Omega

namespace BB429RootMod16

set_option maxHeartbeats 15000000
set_option maxRecDepth 16000

/-- A new all-step obstruction: 7 mod 8 cannot coexist with 7 mod 8
on the actual blank-root return, using the strong positive-even parent. -/
theorem step_not_7_7 (u w a b : Nat)
    (h : BB429Mod8.Allowed u w)
    (heven : 0<u → u%2=0 → w%8=2)
    (hs : BB429.next (u,w)=some (a,b)) :
    a%8=7 → b%8≠7 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [BB429Mod8.Allowed, Prod.mk.injEq, Option.some.injEq]
  all_goals (by_cases hu : 0<u <;> by_cases he : u%2=0 <;>
    (try have hw := heven hu he) <;> omega)

theorem rooted_not_7_7 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) : a%8=7 → b%8≠7 := by
  cases n with
  | zero =>
    simp only [BB429.run, Option.some.injEq, Prod.mk.injEq] at hr
    rcases hr with ⟨rfl,rfl⟩
    omega
  | succ n =>
    simp only [BB429.run] at hr
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp, Option.bind_some] at hr
      exact step_not_7_7 p.1 p.2 a b
        (BB429Mod8.all_blank_returns_allowed n p.1 p.2 hp)
        (fun ha he => BB429RootEven8.rooted_positive_even_eight
          n p.1 p.2 hp ha he)
        hr

/-- An all-step obstruction at 1 mod 16 and 6 mod 8. -/
theorem step_not_1_6 (u w a b : Nat)
    (h : BB429Mod8.Allowed u w)
    (h77 : u%8=7 → w%8≠7)
    (hs : BB429.next (u,w)=some (a,b)) :
    a%16=1 → b%8≠6 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [BB429Mod8.Allowed, Prod.mk.injEq, Option.some.injEq]
  all_goals omega

theorem rooted_not_1_6 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) : a%16=1 → b%8≠6 := by
  cases n with
  | zero =>
    simp only [BB429.run, Option.some.injEq, Prod.mk.injEq] at hr
    rcases hr with ⟨rfl,rfl⟩
    omega
  | succ n =>
    simp only [BB429.run] at hr
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp, Option.bind_some] at hr
      exact step_not_1_6 p.1 p.2 a b
        (BB429Mod8.all_blank_returns_allowed n p.1 p.2 hp)
        (rooted_not_7_7 n p.1 p.2 hp) hr

/-- A direct one-step obstruction at 5 mod 16 and 6 mod 8. -/
theorem step_not_5_6 (u w a b : Nat)
    (h : BB429Mod8.Allowed u w)
    (hs : BB429.next (u,w)=some (a,b)) :
    a%16=5 → b%8≠6 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [BB429Mod8.Allowed, Prod.mk.injEq, Option.some.injEq]
  all_goals omega

theorem rooted_not_5_6 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) : a%16=5 → b%8≠6 := by
  cases n with
  | zero =>
    simp only [BB429.run, Option.some.injEq, Prod.mk.injEq] at hr
    rcases hr with ⟨rfl,rfl⟩
    omega
  | succ n =>
    simp only [BB429.run] at hr
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp, Option.bind_some] at hr
      exact step_not_5_6 p.1 p.2 a b
        (BB429Mod8.all_blank_returns_allowed n p.1 p.2 hp) hr

#print axioms step_not_7_7
#print axioms rooted_not_7_7
#print axioms step_not_1_6
#print axioms rooted_not_1_6
#print axioms step_not_5_6
#print axioms rooted_not_5_6

end BB429RootMod16
