import SpaceNeedleOddBlocks
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0

namespace BB6.Agent48.SpaceNeedle
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD

def splitTwos (n : Nat) : Nat × Nat :=
  if hz : n = 0 then (0, 0)
  else if he : n % 2 = 0 then
    let p := splitTwos (n / 2)
    (p.1 + 1, p.2)
  else (0, n)
termination_by n
decreasing_by omega

theorem splitTwos_spec (n : Nat) (hn : 0<n) :
    n = 2^(splitTwos n).1 * (splitTwos n).2 ∧
    (splitTwos n).2%2=1 ∧ 0<(splitTwos n).2 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases he : n%2=0
    · have hn2 : 0<n/2 := by omega
      have hlt : n/2<n := by omega
      obtain ⟨hfact,hodd,hpos⟩ := ih (n/2) hlt hn2
      have hnonzero : n≠0 := by omega
      have hsplit : splitTwos n = ((splitTwos (n/2)).1+1,(splitTwos (n/2)).2) := by
        rw [splitTwos]
        simp only [dif_neg hnonzero, dif_pos he]
      rw [hsplit]
      refine ⟨?_,hodd,hpos⟩
      calc
        n = 2*(n/2) := by omega
        _ = 2*(2^(splitTwos (n/2)).1*(splitTwos (n/2)).2) :=
          congrArg (fun z : Nat => 2*z) hfact
        _ = 2^((splitTwos (n/2)).1+1)*(splitTwos (n/2)).2 := by
          simp [Nat.pow_succ', Nat.mul_assoc]
    · have hz : n≠0 := by omega
      have hsplit : splitTwos n=(0,n) := by
        rw [splitTwos]
        simp only [dif_neg hz, dif_neg he]
      rw [hsplit]
      simp only [Prod.fst, Prod.snd]
      refine ⟨?_, ?_, hn⟩
      · simp
      · omega

def oddMacroNext (d : Nat) : Option HighLevelState × Nat :=
  if d%2=0 then (highLevelNext (.N d), 1)
  else
    let p := splitTwos (d+1)
    (some (.N (5^p.1*p.2-1)),p.1)

theorem oddMacroNext_sound (d : Nat) (hd : d%2=1) :
    0 < (oddMacroNext d).2 ∧
    runHigh (oddMacroNext d).2 (some (.N d)) = (oddMacroNext d).1 := by
  let p := splitTwos (d+1)
  have hp := splitTwos_spec (d+1) (by omega)
  have hpositive : 0<p.1 := by
    by_cases hzero : p.1=0
    · have heq : d+1=p.2 := by
        have h := hp.1
        change d+1=2^p.1*p.2 at h
        rw [hzero] at h
        simpa using h
      have hodd : p.2%2=1 := hp.2.1
      have heven : (d+1)%2=0 := by omega
      omega
    · omega
  have hfactor : d = 2^p.1*p.2-1 := by
    have h := hp.1
    dsimp [p] at *
    omega
  have hout : runHigh p.1 (some (.N d)) = some (.N (5^p.1*p.2-1)) := by
    rw [hfactor]
    exact odd_block p.1 p.2 hp.2.2
  have hmacro : oddMacroNext d=(some (.N (5^p.1*p.2-1)),p.1) := by
    simp [oddMacroNext,hd,p]
  rw [hmacro]
  exact ⟨hpositive,hout⟩

/-- Every macro return represents a positive number of original exact
high-level steps, uniformly for odd and even source counters. -/
theorem oddMacroNext_sound_all (d : Nat) :
    0 < (oddMacroNext d).2 ∧
    runHigh (oddMacroNext d).2 (some (.N d)) = (oddMacroNext d).1 := by
  by_cases hd : d%2=1
  · exact oddMacroNext_sound d hd
  · have he : d%2=0 := by omega
    simp [oddMacroNext, he, runHigh]

end BB6.Agent48.SpaceNeedle
#print axioms BB6.Agent48.SpaceNeedle.splitTwos_spec
#print axioms BB6.Agent48.SpaceNeedle.oddMacroNext_sound
#print axioms BB6.Agent48.SpaceNeedle.oddMacroNext_sound_all
