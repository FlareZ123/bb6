import RankUniqueness
import P1TwoIff

namespace BB6.P1Rank
open BB6.Agent1

/-- At most one of Agent45's two complete positive feeder families can be
    blank reachable for any given u≥3. The two paths merge after exactly two
    genuine T steps; deterministic strict rank growth forbids two distinct
    blank-reachable immediate predecessors of that root. -/
theorem feeder_lines_mutually_exclusive (u:Nat) (hu:3≤u) :
    ¬(Reach (4*u-4) (4*u+9) ∧ Reach (6*u-2) (2*u+5)) := by
  rintro ⟨ha,hb⟩
  obtain ⟨ha1,ha2⟩ := BB6.Agent45TwoRoot.lower_pair u hu
  obtain ⟨hb1,hb2⟩ := BB6.Agent45Deep2.middle_pair u (by omega)
  have ra : Reach (4*u-1) (4*u+7) :=
    Reach.next _ _ _ _ ha ha1
  have rb : Reach (6*u+1) (2*u+3) :=
    Reach.next _ _ _ _ hb hb1
  have heq := reachable_predecessor_unique
    (4*u-1) (4*u+7) (6*u+1) (2*u+3) (8*u+4) 3
    ra rb ha2 hb2
  omega

/-- The complete two-line reachable feeder condition has exclusive branches. -/
theorem feeder_lines_exclusive_or (u:Nat) (hu:3≤u) :
    (Reach (4*u-4) (4*u+9) ∨ Reach (6*u-2) (2*u+5)) →
    (Reach (4*u-4) (4*u+9) ∧ ¬Reach (6*u-2) (2*u+5)) ∨
    (Reach (6*u-2) (2*u+5) ∧ ¬Reach (4*u-4) (4*u+9)) := by
  intro h
  have hno := feeder_lines_mutually_exclusive u hu
  rcases h with ha | hb
  · exact Or.inl ⟨ha,by intro hb; exact hno ⟨ha,hb⟩⟩
  · exact Or.inr ⟨hb,by intro ha; exact hno ⟨ha,hb⟩⟩

#print axioms BB6.P1Rank.feeder_lines_mutually_exclusive
#print axioms BB6.P1Rank.feeder_lines_exclusive_or
end BB6.P1Rank
