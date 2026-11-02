import HaltingFunnel
import BusyBeaver.BB6.M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE

namespace BB6.P1Bridge

open BB6.HaltingFunnel
open BusyBeaver

namespace Source
export BusyBeaver.M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE
  (HighLevelState evalP2 highLevelNext highLevelStart
   target isHalt_iff_highLevel_acceleration)
end Source

def liftPair (s : Nat × Nat) : Source.HighLevelState :=
  .P_1 s.1 s.2

/-- DeepMind's recursive P2 evaluation is identical to the agent's independently
    defined G recurrence for all k,c, including every recursive branch. -/
theorem G_eq_evalP2 (k c : Nat) :
    Source.evalP2 k c = liftPair (G k c) := by
  induction k using Nat.strongRecOn generalizing c with
  | ind k ih =>
    rw [Source.evalP2, G]
    by_cases hsmall : c < 2*k
    · have hh : ¬ 2*k ≤ c := by omega
      simp only [if_neg hh, dif_pos hsmall]
      have hi : k-(c/2+1) < k := by omega
      have heq : k-c/2-1 = k-(c/2+1) := by omega
      rw [heq]
      exact ih (k-(c/2+1)) hi (2*c+3)
    · have hh : 2*k ≤ c := by omega
      by_cases hnear : c ≤ 2*k+1
      · simp only [if_pos hh, if_pos hnear, dif_neg hsmall]
        rfl
      · have hfar : ¬ c ≤ 2*k+1 := hnear
        simp only [if_pos hh, if_neg hfar, dif_neg hsmall]
        change (liftPair (4*k+4, c-2*k-2)) =
          (liftPair (4*k+4, c-(2*k+2)))
        simp only [liftPair]

/-- All branches of the local one-step P1 accelerator coincide with DeepMind's
    certified high-level transition function after constructor encoding. -/
theorem T_eq_highLevelNext (a c : Nat) :
    Source.highLevelNext (liftPair (a,c)) =
      Option.map liftPair (T a c) := by
  rcases c with _ | _ | c
  · simp [liftPair, T, Source.highLevelNext]
  · simp [liftPair, T, Source.highLevelNext]
  · by_cases heven : a%2=0
    · simp [liftPair, T, Source.highLevelNext, heven]
    · rcases c with _ | _ | c
      · simp [liftPair, T, Source.highLevelNext, heven]
      · simp [liftPair, T, Source.highLevelNext, heven, G_eq_evalP2]
      · simp [liftPair, T, Source.highLevelNext, heven, G_eq_evalP2]

#print axioms G_eq_evalP2
#print axioms T_eq_highLevelNext
end BB6.P1Bridge
