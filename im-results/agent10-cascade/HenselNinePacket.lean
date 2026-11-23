import ForcedThirdValuationSource

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace CascadeHenselNinePacket

/-- The exact 9-step progression modulo 81 underlying the
    unavoidable third-valuation odd source branch. The finite
    arithmetic is checked as a closed decidable proposition:
    multiplication by 18 times a 3-adic unit permutes the nine
    residues {0,9,...,72} modulo 81. No heuristic sampling. -/
theorem complete_nine_lifts_mod81 :
    ∀ x z : Fin 81,
      x.val%9=0 →
      z.val%3≠0 →
      ∃! r : Fin 9, x.val=(18*r.val*z.val)%81 := by
  decide

/-- Parametric lifting of the kernel-certified complete finite
    mod-81 orbit to unbounded natural inputs X and Z. -/
theorem unique_nine_packet_residue
    (X Z : Nat)
    (hX : X%9=0)
    (hZ : Z%3≠0) :
    ∃! r : Fin 9,
      X%81 = (18*r.val*(Z%81))%81 := by
  let x : Fin 81 := ⟨X%81, by omega⟩
  let z : Fin 81 := ⟨Z%81, by omega⟩
  have hx : x.val%9=0 := by
    change (X%81)%9=0
    omega
  have hz : z.val%3≠0 := by
    change (Z%81)%3≠0
    omega
  simpa [x,z] using complete_nine_lifts_mod81 x z hx hz

#print axioms complete_nine_lifts_mod81
#print axioms unique_nine_packet_residue
end CascadeHenselNinePacket
