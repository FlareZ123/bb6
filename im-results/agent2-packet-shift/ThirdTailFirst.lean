import Lean.Elab.Tactic.Omega
import BoundaryPadding
import EThirdTailPhysical
import EZeroFirst
import EOneZeroFullFirst
import EIterDoubleZeroPacket

set_option maxHeartbeats 15000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace BB6.Agent2ThirdTailFirst
open CryptidBoundary BB6.Padding BB6.BoundaryPadding
open BB6.Agent2ThirdTailPhysical
open BB6.Agent2EAltBoundaryFirst

/-- Physical blank-left recognition is invariant under arbitrary finite
    zero padding. The equivalence checks every left-tape position. -/
theorem allFalse_iff (xs : List Bool) :
    xs.all (!·) = true ↔ ∀ n, bitAt xs n = false := by
  induction xs with
  | nil => simp [bitAt]
  | cons b xs ih =>
      constructor
      · intro h n
        cases n with
        | zero =>
            have hb : b = false := by
              cases b <;> simp at h ⊢
            simp [bitAt, hb]
        | succ n =>
            have hxs : xs.all (!·) = true := by
              cases b <;> simpa using h
            exact (ih.mp hxs) n
      · intro h
        have hb : b = false := by
          simpa [bitAt] using (h 0)
        have hx : xs.all (!·) = true := ih.mpr (by
          intro n
          simpa [bitAt] using h (n+1))
        simp [hb,hx]

theorem allFalse_congr {xs ys : List Bool} (h : TapeEq xs ys) :
    (xs.all (!·)=true ↔ ys.all (!·)=true) := by
  rw [allFalse_iff, allFalse_iff]
  constructor
  · intro ha n
    rw [← h n]
    exact ha n
  · intro ha n
    rw [h n]
    exact ha n

/-- The actual observable first-section predicate is invariant under
    complete physical equivalence, not merely under list equality. -/
theorem physical_obs_congr {c d : Cfg} (h : ObsEq c d) :
    Physical c ↔ Physical d := by
  change CfgEq (represent c) (represent d) at h
  rcases h with ⟨hleft,hbit,hright,hstate⟩
  change TapeEq c.l d.l at hleft
  change c.h = d.h at hbit
  change c.st = d.st at hstate
  change (c.st=5 ∧ c.h=false ∧ c.l.all (!·)=true) ↔
    (d.st=5 ∧ d.h=false ∧ d.l.all (!·)=true)
  constructor
  · rintro ⟨hs,hb,hl⟩
    exact ⟨by simpa [hstate] using hs,
      by simpa [hbit] using hb,
      (allFalse_congr hleft).mp hl⟩
  · rintro ⟨hs,hb,hl⟩
    exact ⟨by simpa [hstate] using hs,
      by simpa [hbit] using hb,
      (allFalse_congr hleft).mpr hl⟩

/-- Every earlier physical return has the same truth value in the input
    with and without a terminal explicitly written zero. -/
theorem first_event_unpad (xs : List Bool) (T : Nat)
    (hp : ∀ u, 0<u → u<T →
      ¬ Physical (run u (init (xs ++ [false])))) :
    ∀ u, 0<u → u<T → ¬ Physical (run u (init xs)) := by
  intro u hu ht hphys
  exact hp u hu ht ((physical_obs_congr (source_init_pad u 1 xs)).mp hphys)

/-- q=0 physical third-tail section first returns at its exact endpoint. -/
theorem third_first_q0 (k : Nat) :
    ObsEq (run (12*k*k+49*k+112) (init (thirdWord k 0)))
      (⟨[],false,List.replicate (8*k+3) true ++
        (BB6.Agent32EZero.packetZero ++ List.replicate 8 true),5⟩ : Cfg) ∧
    (∀ u, 0<u → u<12*k*k+49*k+112 →
      ¬ Physical (run u (init (thirdWord k 0)))) := by
  constructor
  · exact third_q0 k
  · apply first_event_unpad
    intro u hu ht hp
    have h := (BB6.Agent2EZeroFirst.full_zero_first_physical k 4 []).2
    apply h u hu (by omega)
    simpa [thirdWord,thirdTail,pairs,List.append_assoc] using hp

/-- q=1 physically unpadded first-return certificate. -/
theorem third_first_q1 (k : Nat) :
    ObsEq (run (12*k*k+49*k+80) (init (thirdWord k 1)))
      (⟨[],false,List.replicate (8*k+3) true ++
        ([true,true,false,true,true,true,true,false] ++
          List.replicate 14 true),5⟩ : Cfg) ∧
    (∀ u, 0<u → u<12*k*k+49*k+80 →
      ¬ Physical (run u (init (thirdWord k 1)))) := by
  constructor
  · exact third_q1 k
  · apply first_event_unpad
    intro u hu ht hp
    have h := (BB6.Agent2EOneZeroFullFirst.full_one_zero_first_physical k 4 []).2
    apply h u hu (by omega)
    simpa [thirdWord,thirdTail,pairs,List.append_assoc] using hp

/-- All q>=2 physically unpadded third-tail inputs have the certified
    first return, with no physically blank-left F/0 event before it. -/
theorem third_first_qge2 (k q : Nat) :
    ObsEq (run (12*k*k+49*k+84+4*q)
      (init (thirdWord k (q+2))))
      (BB6.Agent2EIterDoubleZeroPacket.target k 0 q 4 []) ∧
    (∀ u, 0<u → u<12*k*k+49*k+84+4*q →
      ¬ Physical (run u (init (thirdWord k (q+2))))) := by
  constructor
  · exact third_qge2 k q
  · apply first_event_unpad
    intro u hu ht hp
    have h := (BB6.Agent2EIterDoubleZeroPacket.first_physical_packet k 0 q 4 []).2
    apply h u hu (by dsimp [BB6.Agent2EIterDoubleZeroPacket.duration]; omega)
    simpa [thirdWord,thirdTail,BB6.Agent2EIterDoubleZeroPacket.source,
      pairs,List.append_assoc] using hp

#print axioms physical_obs_congr
#print axioms first_event_unpad
#print axioms third_first_q0
#print axioms third_first_q1
#print axioms third_first_qge2
end BB6.Agent2ThirdTailFirst
