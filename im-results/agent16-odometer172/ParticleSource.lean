import Word
import ParticleWord
import BusyBeaver.BB6.Accelerations.M_1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RBHHH

namespace Odometer172
open BusyBeaver
open BusyBeaver.M_1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RBHHH

theorem bump_source (q : List Nat) : BusyBeaver.Stack.bumpHead q = bump q := by
  cases q <;> rfl

theorem ret_source (m : Bool) (bs : List Bool) (q : List Nat) :
    retHL m bs q = ret m bs q := by
  induction m, bs, q using ret.induct <;>
    simp [retHL, ret, bump_source, *]

theorem scan_source (m : Bool) (bs : List Bool) (q : List Nat) :
    scanHL m bs q = (scan m bs q).map HighLevelState.E := by
  induction q generalizing m bs with
  | nil => cases m <;> simp [scanHL, scan, ret_source]
  | cons d q ih =>
    simp only [scanHL, scan, bm]
    split <;> rename_i h0
    · simp [ret_source]
    · split <;> rename_i h1
      · simp [ret_source]
      · split
        · exact ih _ _
        · split
          · exact ih _ _
          · rfl

theorem particle_source_step {s t : ParticleState} (h : ParticleStep s t) :
    highLevelNext (.E s.encode) = some (.E t.encode) := by
  rw [highLevelNext, scan_source, particle_step_scan h]
  rfl

theorem particle_source_root :
    HighLevelState.E rootParticle.encode = highLevelStart := rfl

#print axioms particle_source_step
#print axioms particle_source_root
end Odometer172
