import RawTokenReturn
import TM62MathlibD0Adapter

namespace BB6.Portfolio
open BB6.CryptidD0Bridge

/-- Every lifted external halting cylinder supplies a halting token parameter. -/
theorem tokenT_halts_on_cylinder (k : Nat) :
    ∃ n, D0HaltsAt
      (tokenT (3^108*k + 1975700577069254261393123959451562008800234946348078)) n := by
  obtain ⟨n, hn⟩ := D0_halts_on_A_cylinder k (-3)
  have he : (3^108*k + 1975700577069254261393123959451562008800234946348078)+8 =
      3^108*k + 1975700577069254261393123959451562008800234946348086 := by omega
  have h : ∃ n, tokenHaltsAt
      (F0Pure ((3^108*k + 1975700577069254261393123959451562008800234946348078)+8) (-3)) n :=
    ⟨n, by simpa only [he, tokenHaltsAt, D0HaltsAt] using hn⟩
  exact (tokenT_halting_iff _).2 h

theorem tokenT_not_universally_nonhalting :
    ¬ ∀ s, ¬ ∃ n, D0HaltsAt (tokenT s) n := by
  intro h
  exact h _ (tokenT_halts_on_cylinder 0)

#print axioms tokenT_halts_on_cylinder
#print axioms tokenT_not_universally_nonhalting
end BB6.Portfolio
