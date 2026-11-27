import Word
import Potential
namespace Odometer172

-- A word-level certificate for an arbitrary projected carry.  The
-- exterior increment is represented by literal 2s in the output.
def twos : Nat → List Nat
  | 0 => []
  | n+1 => 2 :: twos n

def falses : Nat → List Bool
  | 0 => []
  | n+1 => false :: falses n

theorem twos_add (n m : Nat) : twos (n+m) = twos n ++ twos m := by
  induction n with
  | zero => simp [twos]
  | succ n ih => simp [Nat.succ_add, twos, ih]

theorem highs_falses (n : Nat) : highs (falses n) = twos n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [falses, highs, twos, ih]

theorem phi_falses (n : Nat) : phi (falses n) = twos n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [falses, phi, twos, ih]

theorem highs_app (p q : List Bool) : highs (p++q) = highs p ++ highs q := by
  induction p with
  | nil => rfl
  | cons d p ih => simp [highs, ih]

theorem phi_app (p q : List Bool) : phi (p++q) = phi p ++ phi q := by
  induction p with
  | nil => rfl
  | cons d p ih => simp [phi, ih, List.append_assoc]

def phaseWord : Phase → List Nat
  | .d => [1,0]
  | .l => [1]
  | .h => [3]

def boundaryWord : Boundary → List Nat
  | .empty => []
  | .zero => [0]
  | .one => [1]

def pword : List Cell → Boundary → List Nat
  | [], z => boundaryWord z
  | (s,g)::xs,z => phaseWord s ++ twos g ++ pword xs z

inductive CarryForm : List Nat → List Nat → Prop
  | endForm (p : List Bool) : CarryForm (highs p) (phi p)
  | oneForm (p : List Bool) (q : List Nat) :
      CarryForm (highs p ++ 1::q) (phi p ++ bump q)

theorem carryForm_prefix (p : List Bool) {w v : List Nat}
    (h : CarryForm w v) : CarryForm (highs p ++ w) (phi p ++ v) := by
  cases h with
  | endForm q =>
    simpa [highs_app, phi_app] using CarryForm.endForm (p++q)
  | oneForm q r =>
    simpa [highs_app, phi_app, List.append_assoc] using CarryForm.oneForm (p++q) r

theorem carry_form {xs ys : List Cell} {z z' : Boundary} {e : Nat}
    (h : Carry xs z ys z' e) :
    CarryForm (pword xs z) (twos e ++ pword ys z') := by
  induction h with
  | wrapEmpty => exact CarryForm.endForm []
  | wrapOne => exact CarryForm.oneForm [] []
  | d g xs z =>
    simpa [pword, phaseWord, twos, highs, phi, bump] using
      CarryForm.oneForm [] (0 :: (twos g ++ pword xs z))
  | l g xs z =>
    simpa [pword, phaseWord, twos, highs, phi, bump] using
      CarryForm.oneForm [] (2 :: (twos g ++ pword xs z))
  | pair g xs z =>
    simpa [pword, phaseWord, twos, highs, phi, bump] using
      CarryForm.oneForm [] (1 :: (twos g ++ pword xs z))
  | pairBoundary => exact CarryForm.oneForm [] [1,0]
  | drainEmpty => exact CarryForm.oneForm [] []
  | drainZero => exact CarryForm.oneForm [] [0]
  | drainOne => exact CarryForm.oneForm [] [1]
  | @h g xs ys z z' e hc ih =>
    have hp := carryForm_prefix (true :: falses g) ih
    simpa [pword, phaseWord, twos, highs, phi, highs_falses, phi_falses,
      twos_add, List.append_assoc] using hp

theorem carryForm_scan {w v : List Nat} (h : CarryForm w v) (n : Nat) :
    scan false [] (twos n ++ w) = some (twos (n+1) ++ v) := by
  cases h with
  | endForm p =>
    simpa [highs_app, phi_app, highs_falses, phi_falses, twos] using
      scan_end (falses n ++ p)
  | oneForm p q =>
    simpa [highs_app, phi_app, highs_falses, phi_falses, twos, List.append_assoc] using
      scan_one (falses n ++ p) q

theorem carry_scan {xs ys : List Cell} {z z' : Boundary} {e : Nat}
    (h : Carry xs z ys z' e) (n : Nat) :
    scan false [] (twos n ++ pword xs z) =
      some (twos (n+1+e) ++ pword ys z') := by
  rw [twos_add, List.append_assoc]
  exact carryForm_scan (carry_form h) n

-- BirthTail either consumes a final 2, replaces a final 3 by a 2,
-- or removes a lone 3 (that case contributes one extra leading 2).
def TailShape (xs ys : List Cell) : Prop :=
  (∃ p : List Bool, pword xs .zero = highs (p++[false]) ++ [0] ∧
      pword ys .one = highs p ++ [1]) ∨
  (∃ p : List Bool, pword xs .zero = highs (p++[true]) ++ [0] ∧
      pword ys .empty = highs (p++[false])) ∨
  (xs = [(.h,0)] ∧ ys = [])

theorem birth_tail_shape {xs ys : List Cell} (h : BirthTail xs ys) :
    TailShape xs ys := by
  induction h with
  | dec g =>
    left
    refine ⟨true :: falses g, ?_, ?_⟩
    · simp [pword, phaseWord, boundaryWord, highs_app, highs, highs_falses,
        twos_add, twos, List.append_assoc]
    · simp [pword, phaseWord, boundaryWord, highs, highs_falses]
  | remove => exact Or.inr (Or.inr ⟨rfl,rfl⟩)
  | replace g =>
    right; left
    refine ⟨true :: falses g, ?_, ?_⟩
    · simp [pword, phaseWord, boundaryWord, highs_app, highs, highs_falses,
        twos, List.append_assoc]
    · simp [pword, phaseWord, boundaryWord, highs_app, highs, highs_falses,
        twos_add, twos, List.append_assoc]
  | @cons g xs ys hne ht ih =>
    rcases ih with ⟨p,hx,hy⟩ | ⟨p,hx,hy⟩ | ⟨hx,hy⟩
    · left
      refine ⟨(true :: falses g) ++ p, ?_, ?_⟩
      · simp [pword, phaseWord, hx, highs_app, highs, highs_falses, List.append_assoc]
      · simp [pword, phaseWord, hy, highs_app, highs, highs_falses, List.append_assoc]
    · right; left
      refine ⟨(true :: falses g) ++ p, ?_, ?_⟩
      · simp [pword, phaseWord, hx, highs_app, highs, highs_falses, List.append_assoc]
      · simp [pword, phaseWord, hy, highs_app, highs, highs_falses, List.append_assoc]
    · exact False.elim (hne hy)

theorem birth_tail_scan {xs ys : List Cell} (h : BirthTail xs ys) (n : Nat) :
    ∃ z e, (ys ≠ [] → e = 0) ∧
      scan false [] (twos n ++ pword xs .zero) =
        some (pword ((.h,n+1+e)::ys) z) := by
  rcases birth_tail_shape h with ⟨p,hx,hy⟩ | ⟨p,hx,hy⟩ | ⟨hx,hy⟩
  · refine ⟨.one,0,fun _ => rfl,?_⟩
    rw [hx]
    simp only [pword, phaseWord, hy, Nat.add_zero]
    simpa [highs_app, highs_falses, bump, twos_add, twos, List.append_assoc] using
      scan_zero_nonempty (falses n ++ p) false []
  · refine ⟨.empty,0,fun _ => rfl,?_⟩
    rw [hx]
    simp only [pword, phaseWord, hy, Nat.add_zero]
    simpa [highs_app, highs_falses, highs, bump, twos_add, twos, List.append_assoc] using
      scan_zero_nonempty (falses n ++ p) true []
  · subst xs
    subst ys
    refine ⟨.empty,1,by simp,?_⟩
    simpa [pword, phaseWord, boundaryWord, highs_app, highs, highs_falses,
      bump, twos_add, twos, List.append_assoc] using
      scan_zero_nonempty (falses n) true []

theorem birth_empty_scan (n : Nat) :
    scan false [] (twos n ++ pword [] .zero) =
      some (pword [(.h,n)] .one) := by
  cases n with
  | zero => rfl
  | succ n =>
    simpa [pword, phaseWord, boundaryWord, highs_app, highs_falses, highs,
      bump, twos_add, twos, List.append_assoc] using
      scan_zero_nonempty (falses n) false []

structure ParticleState where
  lead : Nat
  cells : List Cell
  bound : Boundary
  deriving DecidableEq

def ParticleState.encode (s : ParticleState) : List Nat :=
  twos s.lead ++ pword s.cells s.bound

def rootParticle : ParticleState := ⟨0,[],.zero⟩

-- A sufficient local transition relation. It need not characterize
-- the dynamics outside the safe region.
inductive ParticleStep : ParticleState → ParticleState → Prop
  | carry (n : Nat) {xs ys z z' e} :
      Carry xs z ys z' e →
      ParticleStep ⟨n,xs,z⟩ ⟨n+1+e,ys,z'⟩
  | birthEmpty (n : Nat) :
      ParticleStep ⟨n,[],.zero⟩ ⟨0,[(.h,n)],.one⟩
  | birth (n : Nat) {xs ys z e} :
      BirthTail xs ys → (ys ≠ [] → e = 0) →
      scan false [] (twos n ++ pword xs .zero) =
        some (pword ((.h,n+1+e)::ys) z) →
      ParticleStep ⟨n,xs,.zero⟩ ⟨0,(.h,n+1+e)::ys,z⟩

theorem particle_step_scan {s t : ParticleState} (h : ParticleStep s t) :
    scan false [] s.encode = some t.encode := by
  cases h with
  | carry n hc => exact carry_scan hc n
  | birthEmpty n => exact birth_empty_scan n
  | birth n hb he hs => exact hs

theorem particle_progress (s : ParticleState) (hs : safe s.cells) :
    ∃ t, ParticleStep s t := by
  obtain ⟨n,xs,z⟩ := s
  rcases carry_or_birth xs z hs with ⟨ys,z',e,hc⟩ | ⟨hz,hh⟩
  · exact ⟨_,ParticleStep.carry n hc⟩
  · subst z
    by_cases hnil : xs = []
    · subst xs
      exact ⟨_,ParticleStep.birthEmpty n⟩
    · obtain ⟨ys,hb⟩ := birth_tail_exists xs hh hnil
      obtain ⟨z,e,he,hscan⟩ := birth_tail_scan hb n
      exact ⟨_,ParticleStep.birth n hb he hscan⟩

inductive ReachParticle : ParticleState → Prop
  | root : ReachParticle rootParticle
  | step {s t} : ReachParticle s → ParticleStep s t → ReachParticle t

-- The only remaining guard involves the new internal gap at a birth.
def BirthGuard : Prop :=
  ∀ n xs ys, ReachParticle ⟨n,xs,.zero⟩ → safe xs →
    BirthTail xs ys → good (.h,n+1) ys

theorem particle_safe (guard : BirthGuard) {s : ParticleState}
    (hr : ReachParticle s) : safe s.cells := by
  induction hr with
  | root => trivial
  | @step s t hr h ih =>
    cases h with
    | carry n hc => exact carry_safe hc ih
    | birthEmpty n => trivial
    | birth n hb he hs =>
      have ht := birth_tail_safe hb ih
      by_cases hy : _ = []
      · simp [hy, safe, good]
      · rw [he hy, Nat.add_zero]
        exact ⟨guard n _ _ hr ih hb, ht⟩

#print axioms carry_form
#print axioms carry_scan
#print axioms birth_tail_scan
#print axioms particle_step_scan
#print axioms particle_progress
#print axioms particle_safe
end Odometer172
