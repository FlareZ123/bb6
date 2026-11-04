import PreimageCandidates
import SweepInvariant

namespace CascadeSource

set_option maxHeartbeats 30000
set_option maxRecDepth 100000

/-- Computable root-phase overapproximation; one logarithmic witness is enough
    to recognize the dyadic sweep signature. -/
def wellBool (a b : Nat) : Bool :=
  decide (b=0) || decide (b=2) ||
    (decide (b%2=1) && decide (a+2=4*2^(Nat.log2 ((a+2)/4))))

theorem wellBool_complete (a b : Nat) (hw : WellState a b) :
    wellBool a b = true := by
  rcases hw with hb | hb | ⟨m,ha,hodd⟩
  · simp [wellBool,hb]
  · simp [wellBool,hb]
  · have hq : (a+2)/4=2^m := by omega
    have hm : Nat.log2 ((a+2)/4)=m := by rw [hq, Nat.log2_two_pow]
    simp [wellBool,ha,hodd,hm]

/-- Complete finite list of original source C-episode predecessors compatible
    with the proven blank-rooted phase invariant. Invalid candidates are
    rejected by evaluating the *actual* source-indexed Cstep. -/
def preimageEdges (u v : Nat) : List (Nat × Nat) :=
  (preimageCandidates u v).filter (fun s =>
    wellBool s.1 s.2 && decide (Cstep s.1 s.2=some (u,v)))

theorem edge_mem (a b u v : Nat) (hw : WellState a b)
  (he : Cstep a b=some (u,v)) : (a,b) ∈ preimageEdges u v := by
  apply List.mem_filter.mpr
  constructor
  · exact source_well_preimage_complete a b u v hw he
  · simp [wellBool_complete a b hw, he]

/-- A finite backward induction certificate. It fails closed on fuel exhaustion
    or when the root appears, accepting only if every exact well-formed
    predecessor has itself received a certificate. -/
def reverseCert : Nat → (Nat × Nat) → Bool
  | 0, _ => false
  | n+1, s => if s=(2,0) then false else
    (preimageEdges s.1 s.2).all (reverseCert n)

/-- A reverse certificate is sufficient to exclude the goal from the
    full, indefinite authentic post-initial source-C orbit. -/
theorem reverseCert_sound (x : Nat × Nat) :
    ∀ fuel, reverseCert fuel x = true →
      ¬ CascadeSweep.ReachC (2,0) x := by
  intro fuel hc hr
  induction hr generalizing fuel with
  | refl =>
      cases fuel with
      | zero => simp [reverseCert] at hc
      | succ k => simp [reverseCert] at hc
  | @push y z hr he ih =>
      cases fuel with
      | zero => simp [reverseCert] at hc
      | succ fuel =>
          have hne : z ≠ (2,0) := by
            intro hh
            subst z
            simp [reverseCert] at hc
          have hal : (preimageEdges z.1 z.2).all (reverseCert fuel) = true := by
            simpa [reverseCert,hne] using hc
          have hw : WellState y.1 y.2 :=
            CascadeSweep.well_reachable hr (Or.inl rfl)
          have hmem : y ∈ preimageEdges z.1 z.2 :=
            edge_mem y.1 y.2 z.1 z.2 hw he
          have hsub : reverseCert fuel y = true :=
            (List.all_eq_true.mp hal) y hmem
          exact ih _ hsub

#print axioms edge_mem
#print axioms reverseCert_sound

end CascadeSource
