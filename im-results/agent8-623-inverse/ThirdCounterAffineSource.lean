import Agent49ParitySource

/-!
Original-source universal affine shift of the third counter for the #623
ternary evaluator and the entire well-founded B-drain, with no budget,
cone, parity or initial-run restriction.

The unmodified source is google-deepmind/cryptids at
c86f15861709b76042998c5211c7b2f83991621b.  Source compilation,
not the standalone mirror, is the decisive verification.

A successful drain's first output coordinate and its failure status
depend solely on its first two input coordinates.  Its second output
coordinate shifts exactly with the third input coordinate.
This universal structural result does not decide blank-root survival.
-/

namespace BB6.Agent8ThirdCounterAffineSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

def thirdShift (t : Nat) (p : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (p.1,p.2.1,p.2.2+t)

theorem evalA_third_shift (a : Nat) :
    ∀ k m t : Nat, evalA a k (m+t) = (evalA a k m).map (thirdShift t) := by
  induction a with
  | zero =>
    intro k m t
    by_cases h2 : k%3=2
    · simp [evalA,h2,thirdShift]
    · by_cases h0 : k%3=0
      · simp [evalA,h2,h0]
      · simp [evalA,h2,h0,thirdShift]
  | succ a ih =>
    intro k m t
    by_cases h2 : k%3=2
    · simp [evalA,h2,thirdShift]
    · by_cases h0 : k%3=0
      · simp [evalA,h2,h0,thirdShift] <;> omega
      · have hmove : m + t + 2 * (k/3) + 3 =
          (m + 2 * (k/3) +3) + t := by omega
        have hleft : evalA (a+1) k (m+t) =
            evalA a (k/3) (m+t+2*(k/3)+3) := by
          rw [evalA]
          simp [h2,h0]
        have hright : evalA (a+1) k m =
            evalA a (k/3) (m+2*(k/3)+3) := by
          rw [evalA]
          simp [h2,h0]
        rw [hleft, hright, hmove]
        exact ih (k/3) (m+2*(k/3)+3) t

def stateShift (t : Nat) : HighLevelState → HighLevelState
  | .D a d => .D a (d+t)

/-- Every complete B-drain is equivariant under an arbitrary additive
translation of the third input counter.  No finiteness or threshold
hypothesis is imposed on the recursive drain. -/
theorem drainB_third_shift (b : Nat) : ∀ a d t : Nat,
    drainB a b (d+t) = (drainB a b d).map (stateShift t) := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a d t
    rw [drainB,drainB]
    by_cases hb : b=0
    · simp [hb,stateShift]
    · simp only [if_neg hb]
      have hm : d+t+2*b+3 = (d+2*b+3)+t := by omega
      rw [hm,evalA_third_shift]
      cases he : evalA a (b-1) (d+2*b+3) with
      | none => simp [he]
      | some p =>
        rcases p with ⟨aa,bb,dd⟩
        simp only [he,Option.map_some,thirdShift,Option.bind_some]
        by_cases hlt : bb < b
        · simp only [if_pos hlt]
          exact ih bb hlt aa dd t
        · simp [hlt]

/-- The domain of the *entire* recursive B-drain is independent of the
third counter.  This is an unbounded consequence of the exact shift. -/
theorem drainB_none_iff_zero (a b d : Nat) :
    drainB a b d = none ↔ drainB a b 0 = none := by
  have hh := drainB_third_shift b a 0 d
  simp only [Nat.zero_add] at hh
  rw [hh]
  cases hx : drainB a b 0 with
  | none => simp [hx]
  | some x => simp [hx]

/-- Every successful full drain has a unique base output at d=0.
In particular the first output coordinate does not change with d. -/
theorem drainB_base_witness (a b d aa dd : Nat)
    (h : drainB a b d = some (.D aa dd)) :
    ∃ c : Nat, drainB a b 0 = some (.D aa c) ∧ dd=c+d := by
  have hh := drainB_third_shift b a 0 d
  simp only [Nat.zero_add] at hh
  cases he : drainB a b 0 with
  | none =>
      rw [he] at hh
      simp [hh] at h
  | some s =>
      rcases s with ⟨a0,c⟩
      rw [he] at hh
      simp [stateShift] at hh
      rw [hh] at h
      have hp : aa=a0 ∧ dd=c+d := by
        cases h
        exact ⟨rfl,rfl⟩
      exact ⟨c, by simpa [hp.1] using he, hp.2⟩

/-- A two-input-output coherence law, across arbitrary third counters. -/
theorem drainB_output_affine (a b d e x y u v : Nat)
    (hd : drainB a b d = some (.D x y))
    (he : drainB a b e = some (.D u v)) :
    x=u ∧ y+e=v+d := by
  obtain ⟨c,hc,hy⟩ := drainB_base_witness a b d x y hd
  obtain ⟨c',hc',hv⟩ := drainB_base_witness a b e u v he
  rw [hc] at hc'
  cases hc'
  constructor
  · rfl
  · omega

#print axioms evalA_third_shift
#print axioms drainB_third_shift
#print axioms drainB_none_iff_zero
#print axioms drainB_base_witness
#print axioms drainB_output_affine
end BB6.Agent8ThirdCounterAffineSource
