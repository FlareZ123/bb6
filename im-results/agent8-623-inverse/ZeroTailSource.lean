import Agent8FarSectorSource

/-!
Original Cryptids #623 exact zero-first-counter branch and two-step safety.
All source-defined accelerator states with first counter zero and d>=40 have
two successful transitions. A smaller threshold follows by parity; this
uniform statement supports a genuine blank-root theorem.
-/

namespace BB6.Agent8ZeroTailSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

/-- Even zero-first-counter input, exact source transition. -/
theorem zero_even_source (d : Nat) (hd : d%2=0) :
    highLevelNext (.D 0 d) = some (.D d 7) := by
  simp [highLevelNext,hd]

/-- Odd zero-first-counter input, exact source transition. -/
theorem zero_odd_source (d : Nat) (hd : d%2=1) :
    highLevelNext (.D 0 d) = some (.D (d-1) 14) := by
  have hpos : 0<d := by omega
  have hev : evalA (d+1) 1 9 = some (d-1,0,14) := by
    cases d with
    | zero => omega
    | succ d => simp [evalA]
  have hbase : drainB (d-1) 0 14 = some (.D (d-1) 14) := by
    rw [drainB]
    simp
  have hB : drainB (d+1) 2 2 = some (.D (d-1) 14) := by
    rw [drainB]
    simp [hev,hbase]
  simpa [highLevelNext,hd] using hB

/-- Every source state D(0,d), d>=40, has two successful section returns. -/
theorem zero_a_two_step (d : Nat) (hd : 40≤d) :
    ∃aa dd bb ee, highLevelNext (.D 0 d) = some (.D aa dd) ∧
                highLevelNext (.D aa dd) = some (.D bb ee) := by
  by_cases he : d%2=0
  · have hfirst := zero_even_source d he
    obtain ⟨bb,ee,hn⟩ := BB6.Agent8FarSectorSource.farLeftSafe d 7 (by omega)
    exact ⟨d,7,bb,ee,hfirst,hn⟩
  · have hodd : d%2=1 := by omega
    have hfirst := zero_odd_source d hodd
    obtain ⟨bb,ee,hn⟩ := BB6.Agent8FarSectorSource.farLeftSafe (d-1) 14 (by omega)
    exact ⟨d-1,14,bb,ee,hfirst,hn⟩

#print axioms zero_even_source
#print axioms zero_odd_source
#print axioms zero_a_two_step
end BB6.Agent8ZeroTailSource
