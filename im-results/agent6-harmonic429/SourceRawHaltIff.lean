import SourceRawHaltFunnel

namespace BB429ActualHaltIff
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- A true raw-machine blank halt occurs iff the genuine accelerated blank
    orbit reaches one of the six necessary modulo-32 halting gates.
    This is an exact reformulation; reachability of the remaining gates
    is open, so it is not a BB(6) decision. -/
theorem raw_halts_iff_six_gates :
    IsHalt target ↔
      ∃ n u w,
        BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
        highLevelNext (.J u w) = none ∧
        (u%32=3 ∨ u%32=9 ∨ u%32=17 ∨ u%32=21 ∨
         u%32=25 ∨ u%32=29) := by
  constructor
  · exact BB429ActualHaltFunnel.actual_machine_halt_requires_six_gate
  · rintro ⟨n,u,w,hreach,hhalt,_⟩
    apply isHalt_iff_highLevel_acceleration.mpr
    have hh :
        ((Option.bind · highLevelNext)^[n]) (some highLevelStart) =
        some (.J u w) := by
      rw [← BB429ActualHaltFunnel.source_run_eq_iterate]
      exact hreach
    refine ⟨n+1, ?_⟩
    rw [Function.iterate_succ_apply', hh]
    simp [hhalt]

#print axioms raw_halts_iff_six_gates
end BB429ActualHaltIff
