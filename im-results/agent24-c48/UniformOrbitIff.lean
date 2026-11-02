import UniformEdges
import UniformReach
import ReachAffine
import FeederOrbitGeneric
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- Exact blank-orbit reachability equivalence for every positive odd
    feeder index s. The reverse direction uses the genuinely executable
    n=2 source edge, not only a necessary-predecessor argument. -/
theorem uniform_feeder_reach_iff_affine (s : Nat) (hs : 1≤s)
    (hodd : s%2=1) :
    BB6.Agent3.CReach (192*s) (160*s-1) ↔
      BB6.Agent3.CReach (278*s-11) (117*s-4) := by
  constructor
  · exact uniform_feeder_forces_affine s hs hodd
  · rintro ⟨time,hr⟩
    have heq :
        ((44*s-3)+(234*s-6)-2,((234*s-6)-2)/2) =
          (278*s-11,117*s-4) := by
      apply Prod.ext <;> omega
    have hparent :
        ∃ t, BB6.Agent8Section.run secNext t (some (5,1)) =
          some (44*s-3,234*s-6) := by
      apply (BB6.Agent15.blank_reach_iff_affine (44*s-3) (234*s-6)
        (by omega) (by omega) (by omega)).mpr
      refine ⟨time,?_⟩
      rwa [heq]
    obtain ⟨t,ht⟩ := hparent
    have hed : secNext (44*s-3,234*s-6)=some (192*s,160*s-1) :=
      uniform_parent_two_edge s hs
    refine ⟨t+1,?_⟩
    simpa [BB6.Agent8Section.run,ht,hed]

/-- Exact all-time three-link backward equivalence between the low
    (a=1) halting-gateway family and its explicit source affine ancestor. -/
theorem uniform_one_gate_reach_iff_affine (s : Nat) (hs : 1≤s)
    (hodd : s%2=1) :
    BB6.Agent3.CReach 1 (256*s+4) ↔
      BB6.Agent3.CReach (278*s-11) (117*s-4) := by
  have ht : 1≤16*s := by omega
  have h := BB6.Agent3.generic_one_gate_reach_iff (16*s) ht
  have h0 : 16*(16*s)+4=256*s+4 := by omega
  have h1 : 12*(16*s)=192*s := by omega
  have h2 : 10*(16*s)-1=160*s-1 := by omega
  rw [h0,h1,h2] at h
  exact h.trans (uniform_feeder_reach_iff_affine s hs hodd)

#print axioms uniform_feeder_reach_iff_affine
#print axioms uniform_one_gate_reach_iff_affine
end BB6.Agent46
