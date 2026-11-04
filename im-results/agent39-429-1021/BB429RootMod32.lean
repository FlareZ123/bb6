import BB429RootMod16
import Lean.Elab.Tactic.Omega

namespace BB429RootMod32

set_option maxHeartbeats 15000000
set_option maxRecDepth 16000

/-- A quantified one-step rule ruling out the specific source-accessible
5-mod-32 / 1-mod-16 cell, from our earlier 1-mod-16 / 6-mod-8
all-blank-root obstruction and the basic Allowed invariant. -/
theorem step_not_5_1 (u w a b : Nat)
    (h : BB429Mod8.Allowed u w)
    (h16 : u%16=1 → w%8≠6)
    (hs : BB429.next (u,w)=some (a,b)) :
    a%32=5 → b%16≠1 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [BB429Mod8.Allowed, Prod.mk.injEq, Option.some.injEq]
  all_goals omega

theorem rooted_not_5_1 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) : a%32=5 → b%16≠1 := by
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
      exact step_not_5_1 p.1 p.2 a b
        (BB429Mod8.all_blank_returns_allowed n p.1 p.2 hp)
        (BB429RootMod16.rooted_not_1_6 n p.1 p.2 hp) hr

#print axioms step_not_5_1
#print axioms rooted_not_5_1

end BB429RootMod32
