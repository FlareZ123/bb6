import Boundary
import AAlternating

namespace BB6.CryptidBridge

/-- A total projection of Agent31's explicit frozen halt state into
    Agent25's stationary F/1 representation. -/
def project (c : CryptidBoundary.Cfg) : CryptidA.Cfg :=
  match c with
  | ⟨left, bit, right, state⟩ =>
      if state = 6 then ⟨left, true, right, 5⟩
      else ⟨left, bit, right, state⟩

/-- The state accessor is explicit because the two Cfg field names differ. -/
def bState (c : CryptidBoundary.Cfg) : Nat :=
  match c with
  | ⟨_, _, _, state⟩ => state

/-- Copy a configuration of the stationary-halt model to the explicit-halt model. -/
def embed (c : CryptidA.Cfg) : CryptidBoundary.Cfg :=
  ⟨c.left, c.bit, c.right, c.state⟩

theorem project_embed (c : CryptidA.Cfg) (h : c.state ≠ 6) :
    project (embed c) = c := by
  cases c with
  | mk left bit right state => simp [embed, project, h]

theorem embed_project (c : CryptidBoundary.Cfg) (h : bState c ≠ 6) :
    embed (project c) = c := by
  cases c with
  | mk left bit right state => simp [embed, project, h]

/-- One-step semiconjugacy, including all state-6 configurations.
    It does not assume that either machine avoids the halt transition. -/
theorem project_step (c : CryptidBoundary.Cfg) :
    project (CryptidBoundary.step c) = CryptidA.step (project c) := by
  cases c with
  | mk left bit right state =>
    cases bit <;>
    (rcases state with _ | _ | _ | _ | _ | _ | _ | state) <;>
    cases left <;> cases right <;>
    simp [project, CryptidBoundary.step, CryptidA.step,
      CryptidBoundary.goL, CryptidA.goL, CryptidBoundary.goR, CryptidA.goR]

theorem project_run (n : Nat) (c : CryptidBoundary.Cfg) :
    project (CryptidBoundary.run n c) = CryptidA.run n (project c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change project (CryptidBoundary.step (CryptidBoundary.run n c)) =
      CryptidA.step (CryptidA.run n (project c))
    rw [project_step, ih]

theorem project_f0_detect (c : CryptidBoundary.Cfg) (_h : (project c).state = 5)
    (hb : (project c).bit = false) : bState c ≠ 6 := by
  intro hc
  simp [project, hc] at hb

/-- Transfer any exact run ending in F/0 to Agent31's original step semantics.
    The F/1 halt encoding difference is handled by the total projection. -/
theorem transfer_f0 (n : Nat) (c d : CryptidA.Cfg)
    (hc : c.state ≠ 6) (hr : CryptidA.run n c = d)
    (hds : d.state = 5) (hdb : d.bit = false) :
    CryptidBoundary.run n (embed c) = embed d := by
  have he : project (CryptidBoundary.run n (embed c)) = d := by
    rw [project_run, project_embed c hc, hr]
  have hh : bState (CryptidBoundary.run n (embed c)) ≠ 6 :=
    project_f0_detect _ (by rw [he]; exact hds) (by rw [he]; exact hdb)
  calc
    CryptidBoundary.run n (embed c) =
        embed (project (CryptidBoundary.run n (embed c))) :=
      (embed_project _ hh).symm
    _ = embed d := by rw [he]

/-- The complete Agent32 parametric A-boundary theorem in Agent31's
    actual raw-machine semantics, for arbitrary binary suffixes. -/
theorem boundary_a_pairs_triples (m q r : Nat) (ys : List Bool) :
    CryptidBoundary.run
      (12*r*r + (6*(m+q)+29)*r + 2*q + 2*(m+q+4*r)+6)
      (embed (CryptidA.ab m
        (CryptidA.pat q ++ (CryptidA.tblock r ++ (false::ys))))) =
    embed (CryptidA.finish (2*(m+q+4*r)+5) ys) := by
  apply transfer_f0
  · simp [CryptidA.ab]
  · exact CryptidA.a_pairs_triples m q r ys
  · rfl
  · rfl

/-- The corresponding implicit-blank-right A return also transports. -/
theorem boundary_a_pairs_triples_nil (m q r : Nat) :
    CryptidBoundary.run
      (12*r*r + (6*(m+q)+29)*r + 2*q + 2*(m+q+4*r)+6)
      (embed (CryptidA.ab m
        (CryptidA.pat q ++ CryptidA.tblock r))) =
    embed (CryptidA.finish (2*(m+q+4*r)+5) []) := by
  apply transfer_f0
  · simp [CryptidA.ab]
  · exact CryptidA.a_pairs_triples_nil m q r
  · rfl
  · rfl

#print axioms project_step
#print axioms project_run
#print axioms transfer_f0
#print axioms boundary_a_pairs_triples
#print axioms boundary_a_pairs_triples_nil

end BB6.CryptidBridge
