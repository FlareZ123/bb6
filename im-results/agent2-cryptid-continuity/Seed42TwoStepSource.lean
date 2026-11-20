import ERemaining
import BoundaryPadding

set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

namespace BB6.Agent2Seed42TwoStep

open CryptidBoundary BB6.BoundaryPadding

def seed42Input (s : Nat) : DRegular.L :=
  ⟨12288*s+11653,4,0⟩

def seed42Middle (s : Nat) : DRegular.L :=
  ⟨32768*s+31069,1,13⟩

def seed42K0 (r : Nat) : Nat := 32768*r+10355
def seed42K1 (r : Nat) : Nat := 32768*r+21278
def seed42K2 (r : Nat) : Nat := 32768*r+32201

def seed42Out0 (r : Nat) : DRegular.L :=
  ⟨8*seed42K0 r+9,3,10⟩

def seed42Out1 (r : Nat) : DRegular.L :=
  ⟨8*seed42K1 r+39,1,5⟩

def seed42Out2 (r : Nat) : DRegular.L :=
  ⟨8*seed42K2 r+23,0,0⟩

/-- The universal eleven-row original-source certificate. -/
private theorem source_step {s t : DRegular.L}
    (hcanon : DRegular.Canon s)
    (hnext : DRegular.next s = some t) :
    ObsEq
      (run (DRegular.duration s) (DRegularSource.sourceSection s))
      (DRegularSource.sourceSection t) :=
  BB6.ERemaining.source_contract s t hcanon hnext

theorem seed42_first (s : Nat) :
    ObsEq
      (run (DRegular.duration (seed42Input s))
        (DRegularSource.sourceSection (seed42Input s)))
      (DRegularSource.sourceSection (seed42Middle s)) := by
  apply source_step
  · simp [DRegular.Canon, seed42Input] <;> omega
  · have hmod : (12288*s+11653)%3=1 := by omega
    have hdiv : (12288*s+11653-4)/3=4096*s+3883 := by omega
    have hdiv' : (12288*s+11653)/3-1=4096*s+3883 := by omega
    simp [seed42Input, seed42Middle, DRegular.next, hmod, hdiv, hdiv']

theorem seed42_second_mod0 (r : Nat) :
    ObsEq
      (run (DRegular.duration (seed42Middle (3*r)))
        (DRegularSource.sourceSection (seed42Middle (3*r))))
      (DRegularSource.sourceSection (seed42Out0 r)) := by
  apply source_step
  · simp [DRegular.Canon, seed42Middle] <;> omega
  · have hmod :
        (32768*(3*r)+31069)%3=1 := by omega
    have hdiv :
        (32768*(3*r)+31069-4)/3=seed42K0 r := by
      simp [seed42K0]; omega
    have hdiv' :
        (32768*(3*r)+31069)/3-1=seed42K0 r := by
      simp [seed42K0]; omega
    simp [seed42Middle, seed42Out0, seed42K0,
      DRegular.next, hmod, hdiv, hdiv']

theorem seed42_second_mod1 (r : Nat) :
    ObsEq
      (run (DRegular.duration (seed42Middle (3*r+1)))
        (DRegularSource.sourceSection (seed42Middle (3*r+1))))
      (DRegularSource.sourceSection (seed42Out1 r)) := by
  apply source_step
  · simp [DRegular.Canon, seed42Middle] <;> omega
  · have hmod :
        (32768*(3*r+1)+31069)%3=0 := by omega
    have hdiv :
        (32768*(3*r+1)+31069-3)/3=seed42K1 r := by
      simp [seed42K1]; omega
    have hdiv' :
        (32768*(3*r+1)+31069)/3-1=seed42K1 r := by
      simp [seed42K1]; omega
    have hbmod : (13+1)%3=2 := by decide
    have hbdiv : (13+1)/3=4 := by decide
    simp [seed42Middle, seed42Out1, seed42K1,
      DRegular.next, hmod, hdiv, hdiv', hbmod, hbdiv]

theorem seed42_second_mod2 (r : Nat) :
    ObsEq
      (run (DRegular.duration (seed42Middle (3*r+2)))
        (DRegularSource.sourceSection (seed42Middle (3*r+2))))
      (DRegularSource.sourceSection (seed42Out2 r)) := by
  apply source_step
  · simp [DRegular.Canon, seed42Middle] <;> omega
  · have hmod :
        (32768*(3*r+2)+31069)%3=2 := by omega
    have hdiv :
        (32768*(3*r+2)+31069-2)/3=seed42K2 r := by
      simp [seed42K2]; omega
    have hdiv' :
        (32768*(3*r+2)+31069)/3=seed42K2 r := by
      simp [seed42K2]; omega
    simp [seed42Middle, seed42Out2, seed42K2,
      DRegular.next, hmod, hdiv, hdiv']

theorem seed42_two_step_mod0 (r : Nat) :
    ObsEq
      (run (DRegular.duration (seed42Input (3*r)) +
            DRegular.duration (seed42Middle (3*r)))
        (DRegularSource.sourceSection (seed42Input (3*r))))
      (DRegularSource.sourceSection (seed42Out0 r)) := by
  exact BB6.BoundaryPadding.source_chain
    (DRegular.duration (seed42Input (3*r)))
    (DRegular.duration (seed42Middle (3*r)))
    (DRegularSource.sourceSection (seed42Input (3*r)))
    (DRegularSource.sourceSection (seed42Middle (3*r)))
    (DRegularSource.sourceSection (seed42Out0 r))
    (seed42_first (3*r))
    (seed42_second_mod0 r)

theorem seed42_two_step_mod1 (r : Nat) :
    ObsEq
      (run (DRegular.duration (seed42Input (3*r+1)) +
            DRegular.duration (seed42Middle (3*r+1)))
        (DRegularSource.sourceSection (seed42Input (3*r+1))))
      (DRegularSource.sourceSection (seed42Out1 r)) := by
  exact BB6.BoundaryPadding.source_chain
    (DRegular.duration (seed42Input (3*r+1)))
    (DRegular.duration (seed42Middle (3*r+1)))
    (DRegularSource.sourceSection (seed42Input (3*r+1)))
    (DRegularSource.sourceSection (seed42Middle (3*r+1)))
    (DRegularSource.sourceSection (seed42Out1 r))
    (seed42_first (3*r+1))
    (seed42_second_mod1 r)

theorem seed42_two_step_mod2 (r : Nat) :
    ObsEq
      (run (DRegular.duration (seed42Input (3*r+2)) +
            DRegular.duration (seed42Middle (3*r+2)))
        (DRegularSource.sourceSection (seed42Input (3*r+2))))
      (DRegularSource.sourceSection (seed42Out2 r)) := by
  exact BB6.BoundaryPadding.source_chain
    (DRegular.duration (seed42Input (3*r+2)))
    (DRegular.duration (seed42Middle (3*r+2)))
    (DRegularSource.sourceSection (seed42Input (3*r+2)))
    (DRegularSource.sourceSection (seed42Middle (3*r+2)))
    (DRegularSource.sourceSection (seed42Out2 r))
    (seed42_first (3*r+2))
    (seed42_second_mod2 r)

#print axioms seed42_first
#print axioms seed42_second_mod0
#print axioms seed42_second_mod1
#print axioms seed42_second_mod2
#print axioms seed42_two_step_mod0
#print axioms seed42_two_step_mod1
#print axioms seed42_two_step_mod2

end BB6.Agent2Seed42TwoStep
