import Lean.Elab.Tactic.Omega

namespace BB6.Agent9Mod7Slack

/-- Exact scalar-energy transitions for the three low inverse depths.
The state variable B is the source offset m+n+6. -/
def LowStep (P I B I' B' : Int) : Prop :=
  (B' = B + 1 ∧ 2 * I' = I - 588 * P + 84 * B - 232) ∨
  (B' = B + 2 ∧ 4 * I' = I - 392 * P + 56 * B - 136) ∨
  (B' = B + 3 ∧ 8 * I' = I)

/-- A finite sequence of depth-0/1/2 scalar transitions. -/
inductive LowTrace (P : Int) : Int → Int → Int → Int → Prop where
  | refl (I B : Int) : LowTrace P I B I B
  | step {I B I' B' J C : Int}
      (h : LowStep P I B I' B') (tail : LowTrace P I' B' J C) :
      LowTrace P I B J C

/-- The energy at the exact shifted wall is always divisible by 16. -/
theorem wall_energy_mod16 (B : Int) :
    (-112 * B + 384) % 16 = 0 := by
  omega

/-- An odd scalar energy cannot be continued by any depth-0/1/2 edge,
and cannot itself be the shifted-wall energy. -/
theorem no_wall_from_odd
    (P I B J C : Int)
    (hI : I % 2 = 1)
    (htrace : LowTrace P I B J C)
    (hwall : J = -112 * C + 384) : False := by
  induction htrace with
  | refl I B =>
      have hw := wall_energy_mod16 B
      omega
  | @step I B I' B' J C hstep tail ih =>
      rcases hstep with ⟨hB, hEq⟩ | ⟨hB, hEq⟩ | ⟨hB, hEq⟩ <;> omega

/-- A state with energy 2 modulo 4 cannot reach the wall through low
transitions: its only possible next edge is depth zero, which makes the
energy odd. -/
theorem no_wall_from_two_mod_four
    (P I B J C : Int)
    (hI : I % 4 = 2)
    (htrace : LowTrace P I B J C)
    (hwall : J = -112 * C + 384) : False := by
  induction htrace with
  | refl I B =>
      have hw := wall_energy_mod16 B
      omega
  | @step I B I' B' J C hstep tail ih =>
      rcases hstep with ⟨hB, hEq⟩ | ⟨hB, hEq⟩ | ⟨hB, hEq⟩
      · have hI' : I' % 2 = 1 := by omega
        exact no_wall_from_odd P I' B' J C hI' tail hwall
      · omega
      · omega

/-- For an initial post-depth-two energy 20, an even first-shallow offset
leaves no route to the wall. A first depth-one edge produces odd energy; a
first depth-zero edge produces energy 2 mod 4, after which only one more
zero-depth edge is possible and it produces odd energy. -/
theorem no_wall_after_twenty_even_offset
    (P T I1 B1 J C : Int)
    (hP : P % 2 = 0)
    (hT : T % 2 = 0)
    (hfirst :
      (B1 = T + 1 ∧ 2 * I1 = 20 - 588 * P + 84 * T - 232) ∨
      (B1 = T + 2 ∧ 4 * I1 = 20 - 392 * P + 56 * T - 136))
    (htrace : LowTrace P I1 B1 J C)
    (hwall : J = -112 * C + 384) : False := by
  rcases hfirst with ⟨hB, hEq⟩ | ⟨hB, hEq⟩
  · have hI : I1 % 4 = 2 := by omega
    exact no_wall_from_two_mod_four P I1 B1 J C hI htrace hwall
  · have hI : I1 % 2 = 1 := by omega
    exact no_wall_from_odd P I1 B1 J C hI htrace hwall

/-- If the post-depth-two energy is 2 mod 4, the first shallow edge must
be depth zero and its output is odd, independently of the offset. -/
theorem no_wall_after_two_mod_four_first_shallow
    (P T Is I1 B1 J C : Int)
    (hIs : Is % 4 = 2)
    (hfirst :
      (B1 = T + 1 ∧ 2 * I1 = Is - 588 * P + 84 * T - 232) ∨
      (B1 = T + 2 ∧ 4 * I1 = Is - 392 * P + 56 * T - 136))
    (htrace : LowTrace P I1 B1 J C)
    (hwall : J = -112 * C + 384) : False := by
  rcases hfirst with ⟨hB, hEq⟩ | ⟨hB, hEq⟩
  · have hI : I1 % 2 = 1 := by omega
    exact no_wall_from_odd P I1 B1 J C hI htrace hwall
  · omega

/-- An odd post-depth-two energy cannot begin a shallow transition. -/
theorem no_first_shallow_from_odd
    (P T Is I1 B1 : Int)
    (hIs : Is % 2 = 1)
    (hfirst :
      (B1 = T + 1 ∧ 2 * I1 = Is - 588 * P + 84 * T - 232) ∨
      (B1 = T + 2 ∧ 4 * I1 = Is - 392 * P + 56 * T - 136)) : False := by
  rcases hfirst with ⟨hB, hEq⟩ | ⟨hB, hEq⟩ <;> omega

/-- After the first shallow edge, the finite mod-7 candidate list reduces
exactly to Is = 48, or Is = 20 with odd first-shallow offset. -/
theorem remaining_slack_candidates
    (P T Is I1 B1 J C : Int)
    (hP : P % 2 = 0)
    (hIs : Is = 6 ∨ Is = 13 ∨ Is = 20 ∨ Is = 27 ∨ Is = 34 ∨ Is = 41 ∨ Is = 48)
    (hfirst :
      (B1 = T + 1 ∧ 2 * I1 = Is - 588 * P + 84 * T - 232) ∨
      (B1 = T + 2 ∧ 4 * I1 = Is - 392 * P + 56 * T - 136))
    (htrace : LowTrace P I1 B1 J C)
    (hwall : J = -112 * C + 384) :
      (Is = 20 ∧ T % 2 = 1) ∨ Is = 48 := by
  rcases hIs with h6 | h13 | h20 | h27 | h34 | h41 | h48
  · have hmod : Is % 4 = 2 := by omega
    exact False.elim (no_wall_after_two_mod_four_first_shallow
      P T Is I1 B1 J C hmod hfirst htrace hwall)
  · have hodd : Is % 2 = 1 := by omega
    exact False.elim (no_first_shallow_from_odd P T Is I1 B1 hodd hfirst)
  · subst Is
    by_cases hTeven : T % 2 = 0
    · exact False.elim (no_wall_after_twenty_even_offset
        P T I1 B1 J C hP hTeven hfirst htrace hwall)
    · exact Or.inl ⟨rfl, by omega⟩
  · have hodd : Is % 2 = 1 := by omega
    exact False.elim (no_first_shallow_from_odd P T Is I1 B1 hodd hfirst)
  · have hmod : Is % 4 = 2 := by omega
    exact False.elim (no_wall_after_two_mod_four_first_shallow
      P T Is I1 B1 J C hmod hfirst htrace hwall)
  · have hodd : Is % 2 = 1 := by omega
    exact False.elim (no_first_shallow_from_odd P T Is I1 B1 hodd hfirst)
  · exact Or.inr h48

#print axioms no_wall_from_odd
#print axioms no_wall_from_two_mod_four
#print axioms no_wall_after_twenty_even_offset
#print axioms no_wall_after_two_mod_four_first_shallow
#print axioms no_first_shallow_from_odd
#print axioms remaining_slack_candidates

end BB6.Agent9Mod7Slack
