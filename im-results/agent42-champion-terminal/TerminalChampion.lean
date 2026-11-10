import TerminalBridge
import ChampionRootBridge
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.TerminalBridge

/-- The physical terminal theorem uses exactly Agent48's source TM63 table. -/
theorem tm63_eq_tm2 : tm63 = Agent48Champion.tm2 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by
    have h := q.isLt
    omega
  rcases hq with hh|hh|hh|hh|hh|hh <;> subst q <;> cases b <;> decide

/-- Literal source S1 terminal sections execute the exact counted number of
    successful primitive steps then encounter an undefined TM63 rule. -/
theorem tm2_terminal_query (L a b : Nat) (h : Int) :
 ∃ c : BB6Coverage.Config,
    BB6Coverage.run Agent48Champion.tm2 (59+12*(L+a))
      ⟨3,h,TerminalFinish.literalS1Tape L a b h⟩ = some c ∧
    BB6Coverage.run Agent48Champion.tm2 (59+12*(L+a)+1)
      ⟨3,h,TerminalFinish.literalS1Tape L a b h⟩ = none := by
  obtain ⟨c,hr,hq,hh,ht⟩ := tm63_terminal_exact L a b h
  rw [tm63_eq_tm2] at hr
  refine ⟨c,hr,?_⟩
  simp only [BB6Coverage.run, hr, Option.bind_some]
  have hz : Agent48Champion.tm2 (BB6Coverage.readSlot c) = none := by
    change Agent48Champion.tm2 (c.state,c.tape c.head) = none
    rw [hq,hh,ht]
    rfl
  simp [BB6Coverage.rawStep,hz]


/-- Exact final-query count for every genuine S1 terminal section, with
    arbitrary tape exterior and unmodified source TM63 semantics. -/
theorem tm2_terminal_query_any_tape (L a : Nat) (t : Int → Bool) (h : Int)
    (H : TerminalFinish.SectionBits L a t h) :
    ∃ c : BB6Coverage.Config,
      BB6Coverage.run Agent48Champion.tm2 (59+12*(L+a)) ⟨3,h,t⟩ = some c ∧
      BB6Coverage.run Agent48Champion.tm2 (59+12*(L+a)+1) ⟨3,h,t⟩ = none := by
  obtain ⟨out,hr,ht⟩ := TerminalFinish.terminalExact L a t h H
  have htransport := run_transport (59+12*(L+a)) (⟨3,h,t⟩ : TerminalFinish.Conf)
    (by change 3 < 6; decide)
  rw [hr] at htransport
  have hseen : BB6Coverage.run Agent48Champion.tm2 (59+12*(L+a)) ⟨3,h,t⟩ =
      some (embed ⟨0,h+7,out⟩) := by
    rw [← tm63_eq_tm2]
    exact htransport.symm
  refine ⟨embed ⟨0,h+7,out⟩, hseen, ?_⟩
  simp only [BB6Coverage.run, hseen, Option.bind_some]
  have hz : Agent48Champion.tm2 (BB6Coverage.readSlot (embed ⟨0,h+7,out⟩)) = none := by
    simp [BB6Coverage.readSlot,embed,Agent48Champion.tm2,ht]
  simp [BB6Coverage.rawStep,hz]

#print axioms tm2_terminal_query_any_tape

#print axioms tm63_eq_tm2
#print axioms tm2_terminal_query
end BB6Coverage.TerminalBridge
