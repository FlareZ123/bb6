import SourceSProjection

namespace Agent9SourceSRun
open BusyBeaver.M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB
open Agent9SProjection
open Agent9SourceSProjection

def scalarRun : Nat → Option (Nat × Nat) → Option (Nat × Nat)
  | 0, x => x
  | n+1, x => (scalarRun n x).bind (fun z => Sstep z.1 z.2)

def sourceRun : Nat → Option HighLevelState → Option HighLevelState
  | 0, x => x
  | n+1, x => (sourceRun n x).bind highLevelNext

theorem live_one_step (b c q d : Nat)
    (h : Sstep (b+16) c = some (q,d)) :
    ∃ b', highLevelNext (.S b c) = some (.S b' d) ∧ q = b'+16 := by
  have hp := projection_exact b c
  rw [h] at hp
  cases hs : highLevelNext (.S b c) with
  | none =>
      simp [projectS, hs] at hp
  | some st =>
      cases st with
      | S b' c' =>
          simp [projectS, hs] at hp
          obtain ⟨hq,hc⟩ := hp
          refine ⟨b', ?_, ?_⟩
          · simpa [hc] using hs
          · omega
      | T m => simp [projectS, hs] at hp
      | Tn j => simp [projectS, hs] at hp
      | Eb k t => simp [projectS, hs] at hp
      | Ed k t => simp [projectS, hs] at hp

theorem transfer_one_step (b c : Nat)
    (h : Sstep (b+16) c = none) :
    ∃ m, highLevelNext (.S b c) = some (.T m) := by
  have hq : (b+16)%3=0 := by
    unfold Sstep at h
    by_cases hq : (b+16)%3=0
    · exact hq
    · by_cases h1 : (b+16)%3=1
      · simp [hq,h1] at h
      · simp [hq,h1] at h
  have hc : c=0 := by
    simp [Sstep, hq] at h
    exact h
  have hb0 : b%3 ≠ 0 := by omega
  have hb1 : b%3 ≠ 1 := by omega
  refine ⟨4*(b/3)+7, ?_⟩
  simp [highLevelNext, hb0,hb1,hc]
  omega

theorem live_source_steps :
    ∀ (n b c q d : Nat),
      scalarRun n (some (b+16,c)) = some (q,d) →
      ∃ b', q = b'+16 ∧
        sourceRun n (some (.S b c)) = some (.S b' d) := by
  intro n
  induction n with
  | zero =>
      intro b c q d h
      simp [scalarRun] at h
      rcases h with ⟨hq,hc⟩
      subst q
      subst d
      exact ⟨b,rfl,rfl⟩
  | succ n ih =>
      intro b c q d h
      cases hr : scalarRun n (some (b+16,c)) with
      | none =>
          simp [scalarRun, hr] at h
      | some z =>
          cases z with
          | mk q1 d1 =>
              obtain ⟨b1,hq1,hs1⟩ := ih b c q1 d1 hr
              have hz : Sstep (b1+16) d1 = some (q,d) := by
                simpa [scalarRun, hr, hq1] using h
              obtain ⟨b2,hs2,hq2⟩ := live_one_step b1 d1 q d hz
              refine ⟨b2,hq2, ?_⟩
              change (sourceRun n (some (.S b c))).bind highLevelNext =
                some (.S b2 d)
              rw [hs1]
              simpa using hs2

theorem first_transfer_source (n b c q d : Nat)
    (hlive : scalarRun n (some (b+16,c)) = some (q,d))
    (htransfer : scalarRun (n+1) (some (b+16,c)) = none) :
    ∃ b' m, q = b'+16 ∧
      sourceRun n (some (.S b c)) = some (.S b' d) ∧
      sourceRun (n+1) (some (.S b c)) = some (.T m) := by
  obtain ⟨b', hq, hs⟩ := live_source_steps n b c q d hlive
  have hzero : Sstep (b'+16) d = none := by
    simpa [scalarRun, hlive, hq] using htransfer
  obtain ⟨m, hm⟩ := transfer_one_step b' d hzero
  refine ⟨b', m, hq, hs, ?_⟩
  change (sourceRun n (some (.S b c))).bind highLevelNext = some (.T m)
  rw [hs]
  simpa using hm

#print axioms live_one_step
#print axioms transfer_one_step
#print axioms live_source_steps
#print axioms first_transfer_source
end Agent9SourceSRun
