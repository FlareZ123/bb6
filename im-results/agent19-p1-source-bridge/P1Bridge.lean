module

public import BusyBeaver.BB6.M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE
public import HaltingFunnel

@[expose] public section

namespace BB6.P1Bridge

open BusyBeaver
namespace Source
export BusyBeaver.M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE
  (HighLevelState highLevelStart highLevelNext highLevelEncode target evalP2
   is_valid_highLevel_acceleration)
end Source

/-- Map the independently proved P1 pair into the original certified high-level system. -/
def lift : Nat × Nat → Source.HighLevelState
  | (a,c) => .P_1 a c

/-- Every branch of the recursive P2 drain agrees with the upstream certified drain. -/
theorem G_agree (k c : Nat) : lift (HaltingFunnel.G k c) = Source.evalP2 k c := by
  induction k using Nat.strongRecOn generalizing c with
  | ind k ih =>
    by_cases hlt : c < 2*k
    · have h0 : ¬ 2*k ≤ c := by omega
      have hsmall : k - (c/2+1) < k := by omega
      rw [HaltingFunnel.G, dif_pos hlt, Source.evalP2, if_neg h0]
      have heq : k - (c/2+1) = k - c/2 - 1 := by omega
      rw [heq]
      exact ih _ hsmall (2*c+3)
    · have hge : 2*k ≤ c := by omega
      by_cases hh : c ≤ 2*k+1
      · rw [HaltingFunnel.G, dif_neg hlt, if_pos hh,
          Source.evalP2, if_pos hge, if_pos hh]
        rfl
      · rw [HaltingFunnel.G, dif_neg hlt, if_neg hh,
          Source.evalP2, if_pos hge, if_neg hh]
        have heq : c - (2*k+2) = c - 2*k - 2 := by omega
        rw [heq]
        rfl

/-- Entire standalone accelerator agrees with the high-level certified transition. -/
theorem T_agree (a c : Nat) :
    Source.highLevelNext (lift (a,c)) = Option.map lift (HaltingFunnel.T a c) := by
  rcases c with _ | _ | c
  · rfl
  · rfl
  · by_cases ha : a % 2 = 0
    · simp [Source.highLevelNext, HaltingFunnel.T, lift, ha]
    · rcases c with _ | _ | c
      · simp [Source.highLevelNext, HaltingFunnel.T, lift, ha]
      · simp [Source.highLevelNext, HaltingFunnel.T, lift, ha]
        simpa [lift] using (G_agree (a/2) 1).symm
      · simp [Source.highLevelNext, HaltingFunnel.T, lift, ha]
        simpa [lift] using (G_agree (a/2+1) (c+2)).symm

/-- Local transition transported through upstream certification. -/
def nextLocal (s : Nat × Nat) : Option (Nat × Nat) :=
  HaltingFunnel.T s.1 s.2

def encodeLocal (s : Nat × Nat) : Cfg (Fin 2) (Fin 6) :=
  Source.highLevelEncode (lift s)

theorem valid_local : IsValidAcceleration Source.target (2,1) encodeLocal nextLocal := by
  have hv := Source.is_valid_highLevel_acceleration
  refine { init_reaches := ?_, step_some := ?_, step_none := ?_ }
  · simpa only [encodeLocal, Source.highLevelStart, lift] using hv.init_reaches
  · rintro ⟨a,c⟩ ⟨b,d⟩ hn
    have he : Source.highLevelNext (lift (a,c)) = some (lift (b,d)) := by
      rw [T_agree]
      simpa [nextLocal] using congrArg (Option.map lift) hn
    exact hv.step_some _ _ he
  · rintro ⟨a,c⟩ hn
    have he : Source.highLevelNext (lift (a,c)) = none := by
      rw [T_agree]
      simpa [nextLocal] using congrArg (Option.map lift) hn
    exact hv.step_none _ he

/-- Original six-state blank-tape halting iff the *local* P1 map halts. -/
theorem raw_halts_iff :
    IsHalt Source.target ↔ CollatzHalts nextLocal (2,1) :=
  valid_local.isHalt_iff

#print axioms G_agree
#print axioms T_agree
#print axioms valid_local
#print axioms raw_halts_iff
end BB6.P1Bridge
