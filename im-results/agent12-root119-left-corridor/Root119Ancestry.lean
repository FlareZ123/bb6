import Root119BShift
namespace BB6Root119

/-- Three consecutive instructions ending in an exposed B/0 force three right marks. -/
theorem three_step_two_right (a b c d : Conf)
    (hab : next a = some b) (hbc : next b = some c)
    (hcd : next c = some d)
    (hdq : d.q = .B) (hd0 : d.tape d.h = false)
    (hdl : d.tape (d.h-2) = false) :
    d.tape (d.h+1) = true ∧ d.tape (d.h+2) = true ∧ d.tape (d.h+3) = true := by
  rcases c with ⟨qc,hc,tc⟩
  cases qc <;> cases ht : tc hc <;> simp [next, ht] at hcd
  all_goals cases hcd
  all_goals
    rcases b with ⟨qb,hb,tb⟩
    cases qb <;> cases hread : tb hb <;> simp [next, hread] at hbc
    all_goals cases hbc
    all_goals
      subst tc
      simp (disch := omega) [setBit] at *
      try omega
    all_goals
      rcases a with ⟨qa,ha,ta⟩
      cases qa <;> cases haread : ta ha <;> simp [next, haread] at hab
      all_goals cases hab
      all_goals
        subst tb
        simp (disch := omega) [setBit] at *
        try omega

/-- All genuinely reached B/0 configurations with left 101 have two right marks. -/
theorem reached_B0_left101_right11 (d : Conf) (hd : Reach d)
    (hdq : d.q = .B) (hd0 : d.tape d.h = false)
    (hleft2 : d.tape (d.h-2) = false)
    (hleft3 : d.tape (d.h-3) = true) :
    d.tape (d.h+1) = true ∧ d.tape (d.h+2) = true ∧ d.tape (d.h+3) = true := by
  cases hd with
  | initial => simp [blank] at hdq
  | @follow c d hc hcd =>
    cases hc with
    | initial =>
      simp [next, blank] at hcd
      subst d
      simp [setBit] at hleft3
    | @follow b c hb hbc =>
      cases hb with
      | initial =>
        simp [next, blank] at hbc
        subst c
        simp (disch := omega) [next, setBit] at hcd
        subst d
        simp at hdq
      | @follow a b ha hab =>
        exact three_step_two_right a b c d hab hbc hcd hdq hd0 hleft2

/-- Consequently neither an empty nor a one-marked-cell right prefix of fewer than three marks is reachable. -/
theorem reached_B0_left101_no_short_right (d : Conf) (hd : Reach d)
    (hdq : d.q = .B) (hd0 : d.tape d.h = false)
    (hleft2 : d.tape (d.h-2) = false)
    (hleft3 : d.tape (d.h-3) = true)
    (hshort : d.tape (d.h+1) = false ∨ d.tape (d.h+2) = false ∨ d.tape (d.h+3) = false) : False := by
  obtain ⟨h1,h2,h3⟩ := reached_B0_left101_right11 d hd hdq hd0 hleft2 hleft3
  rcases hshort with hs | hs <;> simp_all

#print axioms BB6Root119.three_step_two_right
#print axioms BB6Root119.reached_B0_left101_right11
#print axioms BB6Root119.reached_B0_left101_no_short_right
end BB6Root119
