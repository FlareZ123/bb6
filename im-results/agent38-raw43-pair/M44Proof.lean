import M44Data
import M44Abstract
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent38M44
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

def initial : Macro := ⟨0,[3,0,7],W0,9,0⟩

theorem initialInvariant : Invariant cert initial := by
  refine ⟨?_,3,12,?_,?_,initGood⟩
  · intro h
    rcases h with h | h <;> contradiction
  · exact pushWord_sound cert.left [3,0,7] [] 0 3 .nil initLeft
  · exact pushWord_sound cert.right W0 [] 0 12 .nil initRight

/-- Arbitrarily long authentic prefixes in the projected zipper semantics. -/
theorem live (N : Nat) :
    ∃ t z, N ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some z := by
  obtain ⟨t0,h0⟩ := initial_macro
  obtain ⟨y,t,ht,hy,hr⟩ := live_from cert certClosed emptyL emptyR initial initialInvariant (7*N+6)
  have h0' : run0 table t0 ⟨0,[],[]⟩ = some initial.raw := h0
  have ht' : N ≤ t0+t := by omega
  exact ⟨t0+t,y.raw,ht',join0 h0' hr⟩

/-- Every one of the 25 physical completions of the F0 hole is nonhalting. -/
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨t,c,ht,hr⟩ := live n
  let s : Z := ⟨0,0,[],[]⟩
  have hz : (zrun table t s).map project = some c :=
    (run_project table t s).trans hr
  cases hZ : zrun table t s with
  | none => simp [hZ] at hz
  | some z' =>
    have H := zrun_sound table m hm t s z' hZ
    have hb : embed s = blank := BB6Coverage.Agent31Pump.start_embed
    rw [hb] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

theorem literal_cover (bound : Nat) : Cover (DecidedBelow bound) table :=
  Cover.leaf table (fun m hm => Or.inl (never m hm))

#print axioms initialInvariant
#print axioms live
#print axioms never
#print axioms literal_cover
end BB6.Agent38M44
