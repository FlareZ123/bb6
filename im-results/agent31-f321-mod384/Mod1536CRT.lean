import Mod384Source
import Mod512Source
import Lean.Elab.Tactic.Omega

/-!
Chinese-remainder intersection of two independently kernel-certified
forward quotients, avoiding any 1536²-bit full graph enumeration.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace BB6.Agent31F321CRT
open BB6.Agent31F321Density

def possibleGates1536 : List Nat := [61,115,181,211,235,253,277,325,349,421,445,499,517,523,613,637,661,715,733,805,829,883,901,907,925,949,997,1021,1099,1189,1213,1285,1309,1333,1363,1387,1405,1477,1483]

theorem gate_crt_checker :
 ∀ r : Fin 1536,
   r.val % 384 ∈ BB6.Agent31F321Mod384.possibleGates →
   r.val % 512 ∈ BB6.Agent31F321Mod512.possibleGates →
   r.val ∈ possibleGates1536 := by decide +kernel

/-- Any genuine F321 source-counter halting gate, at any finite time, has
    terminal index among only 39 classes modulo 1536. -/
theorem source_terminal_mod1536_candidates (d n : Nat)
  (hr : CounterReach 1 1 n (d+1) d) :
  d % 1536 ∈ possibleGates1536 := by
  have h384 := BB6.Agent31F321Mod384.terminal_mod384_candidates d n hr
  have h512 := BB6.Agent31F321Mod512.terminal_mod512_candidates d n hr
  have ha : (d % 1536) % 384 = d % 384 := by omega
  have hb : (d % 1536) % 512 = d % 512 := by omega
  exact gate_crt_checker ⟨d % 1536, Nat.mod_lt _ (by decide)⟩
    (by simpa only [ha] using h384)
    (by simpa only [hb] using h512)

#print axioms gate_crt_checker
#print axioms source_terminal_mod1536_candidates
end BB6.Agent31F321CRT
