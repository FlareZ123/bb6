import BlankInvariants
import P1Gate

namespace BB6.Agent50P1

/-- The two independently transcribed G maps are extensionally identical. -/
theorem P1_G_identical (k c : Nat) :
    BB6.Agent1.G k c = BB6.HaltingFunnel.G k c := by
  induction k using Nat.strongRecOn generalizing c with
  | ind k ih =>
    by_cases hlow : c<2*k
    · rw [BB6.Agent1.G, BB6.HaltingFunnel.G]
      simp only [hlow,dite_true]
      exact ih (k-(c/2+1)) (by omega) (2*c+3)
    · by_cases hmid : c≤2*k+1
      · rw [BB6.Agent1.G, BB6.HaltingFunnel.G]
        simp [hlow,hmid]
      · rw [BB6.Agent1.G, BB6.HaltingFunnel.G]
        simp [hlow,hmid]

/-- Exact identity of both published P1 accelerated maps. -/
theorem P1_T_identical (a c : Nat) :
    BB6.Agent1.T a c = BB6.HaltingFunnel.T a c := by
  unfold BB6.Agent1.T BB6.HaltingFunnel.T
  by_cases h0:c=0
  · simp [h0]
  · by_cases h1:c=1
    · simp [h0,h1]
    · by_cases he:a%2=0
      · simp [h0,h1,he]
      · by_cases h2:c=2
        · simp [h0,h1,he,h2]
        · by_cases h3:c=3
          · simp [h0,h1,he,h2,h3,P1_G_identical]
          · simp [h0,h1,he,h2,h3,P1_G_identical]

/-- Exact equivalence of two separately formalized blank-entry finite-reachability predicates. -/
theorem P1_reach_equiv (a c : Nat) :
    BB6.Agent1.Reach a c ↔ BB6.HaltingFunnel.BlankReach a c := by
  constructor
  · intro hr
    induction hr with
    | init => exact BB6.HaltingFunnel.BlankReach.init
    | next a c b d hr ht ih =>
        exact BB6.HaltingFunnel.BlankReach.next a c b d ih
          (by rw [←P1_T_identical]; exact ht)
  · intro hr
    induction hr with
    | init => exact BB6.Agent1.Reach.init
    | next a c b d hr ht ih =>
        exact BB6.Agent1.Reach.next a c b d ih
          (by rw [P1_T_identical]; exact ht)

/-- Restated, directly in Agent4's blank reachability that Agent19 bridged to the original TM. -/
theorem P1_no_critical_10_mod16_source (k : Nat) :
    ¬BB6.HaltingFunnel.BlankReach 2 (14*2^(16*k+10)-2*(16*k+10)-10) := by
  intro h
  have h1 := (P1_reach_equiv _ _).mpr h
  exact blank_no_critical_10_mod16 k h1

/-- Direct transfer to the certified source-oriented reflexive/transitive reach predicate. -/
theorem P1_no_critical_10_mod16_ReachT (k : Nat) :
    ¬BB6.HaltingFunnel.ReachT 2 1 2
      (14*2^(16*k+10)-2*(16*k+10)-10) := by
  intro h
  exact P1_no_critical_10_mod16_source k
    ((BB6.HaltingFunnel.blank_reach_iff_T _ _).mpr h)

#print axioms P1_G_identical
#print axioms P1_T_identical
#print axioms P1_reach_equiv
#print axioms P1_no_critical_10_mod16_source
#print axioms P1_no_critical_10_mod16_ReachT
end BB6.Agent50P1
