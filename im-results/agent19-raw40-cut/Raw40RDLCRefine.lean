import Raw40CanonicalCut
import Raw40RDLCAll
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement BB6.Agent31FourHoleRoster BB6.Agent50TNFPilot

def rdlcRemaining := canonicalRemaining.filter fun e => !sameTable e.2 Raw40RDLC.p

theorem rdlc_count : rdlcRemaining.length = 188 := by decide

theorem rdlc_local_sound : ∀ m, TNFQuotientCompatible parent m → WeightedBound 7014 m ∨
    ∃ e ∈ rdlcRemaining, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases canonical_local_sound m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · by_cases ht : sameTable e.2 Raw40RDLC.p = true
    · have eq : e.2 = Raw40RDLC.p := sameTable_sound ht
      have hb := quotientSafe Raw40RDLC.root Raw40RDLC.all m (eq ▸ hq)
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    · exact Or.inr ⟨e,by simp [rdlcRemaining,he,ht],hq⟩

noncomputable def rdlcRoster := graftRoster parent rdlcRemaining BB6.Agent47CanonicalRaw114Accepted.roster

theorem rdlc_roster_count : rdlcRoster.length = 264 := by decide

theorem rdlc_roster_sound : ∀ m, compatible root m → WeightedBound 7014 m ∨
    ∃ e ∈ rdlcRoster, TNFQuotientCompatible e.2 m :=
  quotient_graft_sound BB6.Agent47CanonicalRaw114Accepted.sound rdlc_local_sound

/-- The bound 106 is attained at delay zero, after 105 ordinary moves. -/
def rdlcWitness : Machine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some ⟨true,true,1⟩
  | 0,true => some ⟨false,true,3⟩
  | 1,false => some ⟨true,true,2⟩
  | 1,true => some ⟨false,false,2⟩
  | 2,false => some ⟨false,true,3⟩
  | 2,true => some ⟨false,false,4⟩
  | 3,false => some ⟨true,false,3⟩
  | 3,true => some ⟨true,false,0⟩
  | 4,false => some ⟨true,true,5⟩
  | 4,true => some ⟨true,false,5⟩
  | 5,false => some ⟨false,true,2⟩
  | _,_ => none

theorem rdlc_witness_compatible : compatible Raw40RDLC.p rdlcWitness := by
  intro s t ht
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> first
    | have h : Raw40RDLC.p (_,_) = none := by decide; rw [h] at ht; contradiction
    | cases ht <;> rfl

theorem rdlc_witness_halts : HaltsAfter rdlcWitness 105 := by
  constructor <;> rfl

theorem rdlc_witness_delay : 0 ∈ delays (zeroNext rdlcWitness) 0 := by decide

theorem rdlc_exact_weighted : (∀ m, compatible Raw40RDLC.p m → WeightedBound 106 m) ∧
    ∀ B < 106, ∃ m, compatible Raw40RDLC.p m ∧ ¬ WeightedBound B m := by
  refine ⟨Raw40RDLC.all,?_⟩
  intro B hB
  refine ⟨rdlcWitness,rdlc_witness_compatible,?_⟩
  intro hb
  have h := hb 105 0 rdlc_witness_halts rdlc_witness_delay
  omega

#print axioms rdlc_roster_sound
#print axioms rdlc_exact_weighted
end BB6.Agent19Raw40
