import BB429Mod8
import Lean.Elab.Tactic.Omega

namespace Agent6RootOddRows

/-- No source transition from an Allowed state enters the residue pair
(first counter 7 mod 8, second counter 6 mod 8). -/
theorem incoming_not_7_6 (u w a b : Nat)
    (h : BB429Mod8.Allowed u w)
    (hs : BB429.next (u,w)=some (a,b))
    (ha : a%8=7) : b%8≠6 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [BB429Mod8.Allowed, Prod.mk.injEq, Option.some.injEq]
  all_goals omega

/-- The 7/6 exclusion is preserved along the genuine blank-root orbit. -/
theorem rooted_not_7_6 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (ha : a%8=7) : b%8≠6 := by
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
      exact incoming_not_7_6 p.1 p.2 a b
        (BB429Mod8.all_blank_returns_allowed n p.1 p.2 hp) hr ha

/-- The next root-row exclusion uses the 7/6 gate as its only extra
hypothesis; the Allowed invariant alone leaves the source predecessor
(7 mod 8, 6 mod 8). -/
theorem incoming_not_1_5 (u w a b : Nat)
    (h : BB429Mod8.Allowed u w)
    (h76 : u%8=7 → w%8≠6)
    (hs : BB429.next (u,w)=some (a,b))
    (ha : a%16=1) : b%8≠5 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [BB429Mod8.Allowed, Prod.mk.injEq, Option.some.injEq]
  all_goals (by_cases h7 : u%8=7 <;>
    (try have hw := h76 h7) <;> omega)

/-- No blank-root state has first counter 1 mod 16 and second counter
5 mod 8. -/
theorem rooted_not_1_5 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (ha : a%16=1) : b%8≠5 := by
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
      exact incoming_not_1_5 p.1 p.2 a b
        (BB429Mod8.all_blank_returns_allowed n p.1 p.2 hp)
        (rooted_not_7_6 n p.1 p.2 hp) hr ha

#print axioms incoming_not_7_6
#print axioms rooted_not_7_6
#print axioms incoming_not_1_5
#print axioms rooted_not_1_5

end Agent6RootOddRows
