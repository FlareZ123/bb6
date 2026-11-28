import SignedPairMacroBridge

/-! Exact pair-type flip modulo 2 for the signed E/S plus even-F words.
    Lean CI acceptance pending. -/
namespace SignedPairMacroBridge

/-- Every typed E/S block, including its even F tail, shifts combined
    rank R=6u+D by 6j+4 or 6j+8 according to its source type. -/
theorem pairRun_rank_delta {typ : Bool} {j u D v d' : Nat}
    (h : PairRun typ j u D v d') :
    6*v+d'=6*u+D+6*j+(if typ then 4 else 8) := by
  have hd : (6*u+D)%2=0 := by
    cases h <;> omega
  let r : Nat := (6*u+D)/2
  have hr : 6*u+D=2*r := by
    dsimp [r]
    omega
  obtain ⟨s,hs,ht⟩ := pairRun_model_exists h hr
  have hstep := ht.2
  dsimp [PeriodicMacro.Step,PeriodicMacro.rankCost] at hstep
  cases typ <;> simp_all <;> omega

theorem pairRun_input_rank_mod4 {typ : Bool} {j u D v d' : Nat}
    (h : PairRun typ j u D v d') :
    (6*u+D)%4=(if typ then 2 else 0) := by
  cases h <;> omega

/-- Source guards force E/S pair type to change iff j is odd.
    This is a consequence of exact rank increments, not a heuristic
    typing rule. -/
theorem successive_pair_type_parity
    {typ typ' : Bool} {j k u D v d' w d'' : Nat}
    (h : PairRun typ j u D v d')
    (next : PairRun typ' k v d' w d'') :
    (typ=typ') ↔ j%2=0 := by
  have hr := pairRun_rank_delta h
  have hi := pairRun_input_rank_mod4 h
  have ho := pairRun_input_rank_mod4 next
  cases typ <;> cases typ' <;> simp_all <;> omega

#print axioms pairRun_rank_delta
#print axioms pairRun_input_rank_mod4
#print axioms successive_pair_type_parity
end SignedPairMacroBridge
