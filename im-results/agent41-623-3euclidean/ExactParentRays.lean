import DrainImageSource

namespace BB6.Agent41ExactParentRays
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49CorrectionGrowth BB6.Agent49InverseWindowSource
open BB6.Agent49FlatDrainSource

private theorem zero_drain (a z : Nat) : drainB a 0 z = some (.D a z) := by
  rw [drainB]; simp

private theorem trace_parity {a b z x y n0 n1 n2 : Nat}
    (h : PositiveTrace a b z x y n0 n1 n2) :
    x%2=(a+b)%2 := by
  induction h with
  | stop => simp
  | r0 hq ha _ ih => omega
  | r1 ha _ ih => omega
  | r2 ha _ ih => omega

def firstInput (x b : Nat) : Nat := ((x:Int)-drift b).toNat

theorem inverse_hit {x y z b : Nat} (hz : z≤5) (hy : 20 < y)
    (hx : 2*inverseBudget y≤ x)
    (h : Agent41DrainImageDecoder.inverse (y-z)= some b) :
    let A := firstInput x b
    inverseBudget y≤ A ∧ (A+b)%2= x%2 ∧
    y= z+image b ∧ 4≤ b ∧ drainB A b z= some (.D x y) := by
  dsimp
  have hi := Agent41DrainImageDecoder.inverse_sound
    Agent41DrainImageSource.excessLaws (y-z) b h
  have hi' : y= z+image b := by unfold image; omega
  have hmin : 4≤ b := by
    by_cases hsmall : 4≤ b
    · exact hsmall
    exfalso
    have hh : b=0 ∨ b=1 ∨ b=2 ∨ b=3 := by omega
    rcases hh with h0|h1|h2|h3
    · subst b; simp [image,excess_zero] at hi'; omega
    · subst b
      have h1 : excess 1=4 := by
        have h := excess_one 0
        simp [excess_zero] at h
        exact h
      simp [image,h1] at hi'; omega
    · subst b
      have h1 : excess 1=4 := by
        have h := excess_one 0
        simp [excess_zero] at h
        exact h
      have h2 : excess 2=6 := by
        have h := excess_two 0
        simpa [h1] using h
      simp [image,h2] at hi'; omega
    · subst b
      have h3 : excess 3=0 := by
        have h := excess_three 1 (by decide)
        simpa [excess_zero] using h
      simp [image,h3] at hi'; omega
  let n := inverseBudget y
  have hyb : y < 2^n := by
    dsimp [n,inverseBudget]
    exact (Nat.log2_lt (by omega)).mp (by omega)
  have hb : b < 2^n := by unfold image at hi'; omega
  obtain ⟨u,v,c0,c1,c2,he,ht⟩ := positive_trace_exists drainB HighLevelState.D
    zero_drain drain_three drain_three_one drain_three_two n n b z (by omega) hb
  have hv := trace_image ht
  have hv' : v= y := by omega
  rw [hv'] at he ht
  have hw := source_drain_window n b z u y he
  unfold Window at hw
  have hd := trace_drift ht
  have hd' : (n:Int)≤(x:Int)-drift b := by omega
  have hA' : (firstInput x b:Int)=(x:Int)-drift b := by
    unfold firstInput
    exact Int.toNat_of_nonneg (by omega)
  have hA : n≤ firstInput x b := by omega
  obtain ⟨u',v',e0,e1,e2,he',ht'⟩ := positive_trace_exists drainB HighLevelState.D
    zero_drain drain_three drain_three_one drain_three_two n (firstInput x b) b z hA hb
  have hv' := trace_image ht'
  have hd'' := trace_drift ht'
  have hu : u'= x := by omega
  have hyy : v'= y := by omega
  rw [hu,hyy] at he' ht'
  exact ⟨hA,(trace_parity ht').symm,hi',hmin,he'⟩

private theorem drain_bundle (A a : Nat) :
    drainB A (a+1) 0 = (evalA A a (2*a+5)).bind fun p => drainB p.1 p.2.1 p.2.2 := by
  conv => lhs; rw [drainB]
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false, Nat.add_sub_cancel]
  have h : 0+2*(a+1)+3=2*a+5 := by omega
  rw [h]
  cases he : evalA A a (2*a+5) with
  | none => rfl
  | some p =>
    rcases p with ⟨a1,b1,d1⟩
    simp only [Option.bind_some]
    have hh := evalA_second_le A a (2*a+5) a1 b1 d1 he
    rw [if_pos (show b1 < a+1 by omega)]

def leftCandidate (x y : Nat) : Option (Nat×Nat) := do
  if y%2=0 then
    let b ← Agent41DrainImageDecoder.inverse (y-2)
    let A := firstInput x b
    return (A+b,b-2)
  else
    let b ← Agent41DrainImageDecoder.inverse (y-5)
    let A := firstInput x b
    return (A+b+2,b-3)

def rightCandidate (x y : Nat) : Option (Nat×Nat) := do
  if y%2=0 then
    let b ← Agent41DrainImageDecoder.inverse (y-3)
    let A := firstInput x b
    return (b+1,A+b-3)
  else
    let b ← Agent41DrainImageDecoder.inverse y
    let A := firstInput x b
    return (b-1,A+b-2)

private theorem budget_ge_five (y : Nat) (hy : 20 < y) : 5≤ inverseBudget y := by
  unfold inverseBudget
  by_cases h : 5≤ y.log2+1
  · exact h
  exfalso
  have hlog : y.log2 < 4 := by omega
  have h' := (Nat.log2_lt (by omega : y≠0)).mp hlog
  omega

theorem leftCandidate_sound {x y a d : Nat} (hy : 20 < y)
    (hx : 2*inverseBudget y≤ x) (heven : x%2=0)
    (h : leftCandidate x y= some (a,d)) :
    a%2=0 ∧ d < a ∧ highLevelNext (.D a d)= some (.D x y) := by
  unfold leftCandidate at h
  split at h
  · rename_i hypar
    cases hb : Agent41DrainImageDecoder.inverse (y-2) with
    | none => simp [hb] at h
    | some b =>
      simp [hb] at h
      obtain ⟨ha,hd⟩ := h
      subst a; subst d
      obtain ⟨hA,hp,hi,hmin,hs⟩ := inverse_hit (z:=2) (by decide) hy hx hb
      have hpar := Agent41DrainImageDecoder.image_parity Agent41DrainImageSource.excessLaws b
      change image b%2= b%2 at hpar
      have hbpar : b%2=0 := by omega
      have hdpar : (b-2)%2=0 := by omega
      have hbudget := budget_ge_five y hy
      refine ⟨by omega,by omega,?_⟩
      have he : firstInput x b+b-(b-2)-2= firstInput x b := by omega
      have hb' : b-2+2= b := by omega
      simp only [highLevelNext,if_neg (show firstInput x b+b≠0 by omega),
        if_neg (show ¬((b-2)%2=1 ∧ firstInput x b+b≥ b-2+5) by omega),
        if_pos (show (b-2)%2=0 ∧ firstInput x b+b≥ b-2+3 by omega),he,hb']
      exact hs
  · rename_i hypar
    cases hb : Agent41DrainImageDecoder.inverse (y-5) with
    | none => simp [hb] at h
    | some b =>
      simp [hb] at h
      obtain ⟨ha,hd⟩ := h
      subst a; subst d
      obtain ⟨hA,hp,hi,hmin,hs⟩ := inverse_hit (z:=5) (by decide) hy hx hb
      have hpar := Agent41DrainImageDecoder.image_parity Agent41DrainImageSource.excessLaws b
      change image b%2= b%2 at hpar
      have hbpar : b%2=0 := by omega
      have hdpar : (b-3)%2=1 := by omega
      refine ⟨by omega,by omega,?_⟩
      have he : firstInput x b+b+2-(b-3)-5= firstInput x b := by omega
      have hb' : b-3+3= b := by omega
      simp only [highLevelNext,if_neg (show firstInput x b+b+2≠0 by omega),
        if_pos (show (b-3)%2=1 ∧ firstInput x b+b+2≥ b-3+5 by omega),he,hb']
      exact hs

theorem rightCandidate_sound {x y a d : Nat} (hy : 20 < y)
    (hx : 2*inverseBudget y≤ x) (heven : x%2=0)
    (h : rightCandidate x y= some (a,d)) :
    a%2=0 ∧ a < d ∧ highLevelNext (.D a d)= some (.D x y) := by
  unfold rightCandidate at h
  split at h
  · rename_i hypar
    cases hb : Agent41DrainImageDecoder.inverse (y-3) with
    | none => simp [hb] at h
    | some b =>
      simp [hb] at h
      obtain ⟨ha,hd⟩ := h
      subst a; subst d
      obtain ⟨hA,hp,hi,hmin,hs⟩ := inverse_hit (z:=3) (by decide) hy hx hb
      have hpar := Agent41DrainImageDecoder.image_parity Agent41DrainImageSource.excessLaws b
      change image b%2= b%2 at hpar
      have hbpar : b%2=1 := by omega
      have hdpar : (firstInput x b+b-3)%2=1 := by omega
      have hbudget := budget_ge_five y hy
      refine ⟨by omega,by omega,?_⟩
      have he : firstInput x b+b-3+4-(b+1)= firstInput x b := by omega
      have hb' : b+1-1= b := by omega
      simp only [highLevelNext,if_neg (show b+1≠0 by omega),
        if_neg (show ¬((firstInput x b+b-3)%2=1 ∧ b+1≥ firstInput x b+b-3+5) by omega),
        if_neg (show ¬((firstInput x b+b-3)%2=0 ∧ b+1≥ firstInput x b+b-3+3) by omega),
        if_neg (show (b+1)%2≠1 by omega),
        if_neg (show b+1≠firstInput x b+b-3+2 by omega),if_pos hdpar,he,hb']
      exact hs
  · rename_i hypar
    cases hb : Agent41DrainImageDecoder.inverse y with
    | none => simp [hb] at h
    | some b =>
      simp [hb] at h
      obtain ⟨ha,hd⟩ := h
      subst a; subst d
      have hb0 : Agent41DrainImageDecoder.inverse (y-0)= some b := by simpa using hb
      obtain ⟨hA,hp,hi,hmin,hs⟩ := inverse_hit (z:=0) (by decide) hy hx hb0
      have hpar := Agent41DrainImageDecoder.image_parity Agent41DrainImageSource.excessLaws b
      change image b%2= b%2 at hpar
      have hbpar : b%2=1 := by omega
      have hdpar : (firstInput x b+b-2)%2=0 := by omega
      have hbudget := budget_ge_five y hy
      refine ⟨by omega,by omega,?_⟩
      have he : firstInput x b+b-2+1-(b-1)= firstInput x b := by omega
      have hb' : b-1+1= b := by omega
      simp only [highLevelNext,if_neg (show b-1≠0 by omega),
        if_neg (show ¬((firstInput x b+b-2)%2=1 ∧ b-1≥ firstInput x b+b-2+5) by omega),
        if_neg (show ¬((firstInput x b+b-2)%2=0 ∧ b-1≥ firstInput x b+b-2+3) by omega),
        if_neg (show (b-1)%2≠1 by omega),
        if_neg (show b-1≠firstInput x b+b-2+2 by omega),
        if_neg (show (firstInput x b+b-2)%2≠1 by omega),he]
      rw [←drain_bundle,hb']
      exact hs


private def Reconstructed (A b z x y : Nat) : Prop :=
  Window A b z x y ∧
  (2*inverseBudget y≤ x →
    y= z+image b ∧ Agent41DrainImageDecoder.inverse (y-z)= some b ∧ firstInput x b= A)

private theorem reconstructed_of_drain (A b z x y : Nat)
    (h : drainB A b z= some (.D x y)) : Reconstructed A b z x y := by
  refine ⟨source_drain_window A b z x y h,?_⟩
  intro hx
  obtain ⟨n0,n1,n2,ht⟩ := source_large_first_trace A b z x y h hx
  have hi := trace_image ht
  have hd := trace_drift ht
  have hg : y-z= image b := by omega
  refine ⟨hi,by rw [hg]; exact Agent41DrainImageSource.image_decoder b,?_⟩
  unfold firstInput
  omega

/-- Complete two-candidate inverse for all large-first even outputs.
No candidate reevaluation or search over the block counter is necessary. -/
theorem exact_parent_candidates {a d x y : Nat} (hy : 20 < y)
    (hx : 2*inverseBudget y≤ x) (heven : x%2=0) :
    highLevelNext (.D a d)= some (.D x y) ↔
      leftCandidate x y= some (a,d) ∨ rightCandidate x y= some (a,d) := by
  constructor
  · intro h
    have hp := parent_envelope_complete Reconstructed reconstructed_of_drain a d x y h
    have hn := budget_ge_five y hy
    unfold ParentEnvelope at hp
    rcases hp with haxis|hlo|hle|hdiag|hro|hre
    · rcases haxis.2 with h|h <;> omega
    · obtain ⟨A,b,hd,_,ha,hdb,hP⟩ := hlo
      obtain ⟨hi,hg,hA⟩ := hP.2 hx
      have hpar := Agent41DrainImageDecoder.image_parity Agent41DrainImageSource.excessLaws b
      change image b%2= b%2 at hpar
      have hypar : y%2≠0 := by omega
      left
      simp [leftCandidate,hypar,hg,hA,show b-3= d by omega,←ha]
    · obtain ⟨A,b,hd,_,ha,hdb,hP⟩ := hle
      obtain ⟨hi,hg,hA⟩ := hP.2 hx
      have hpar := Agent41DrainImageDecoder.image_parity Agent41DrainImageSource.excessLaws b
      change image b%2= b%2 at hpar
      have hypar : y%2=0 := by omega
      left
      simp [leftCandidate,hypar,hg,hA,show b-2= d by omega,←ha]
    · obtain ⟨_,_,hw,_⟩ := hdiag
      unfold Window at hw
      omega
    · obtain ⟨A,b,ha,hd,hab,hdb,hP⟩ := hro
      obtain ⟨hi,hg,hA⟩ := hP.2 hx
      have hpar := Agent41DrainImageDecoder.image_parity Agent41DrainImageSource.excessLaws b
      change image b%2= b%2 at hpar
      have hypar : y%2=0 := by omega
      right
      simp [rightCandidate,hypar,hg,hA,show A+b-3= d by omega,←hab]
    · obtain ⟨A,b,ha,hd,hab,hdb,hP⟩ := hre
      obtain ⟨hi,hg,hA⟩ := hP.2 hx
      have hpar := Agent41DrainImageDecoder.image_parity Agent41DrainImageSource.excessLaws b
      change image b%2= b%2 at hpar
      have hypar : y%2≠0 := by omega
      right
      simp only [Nat.sub_zero] at hg
      simp [rightCandidate,hypar,hg,hA,show A+b-2= d by omega,show b-1= a by omega]
  · rintro (h|h)
    · exact (leftCandidate_sound hy hx heven h).2.2
    · exact (rightCandidate_sound hy hx heven h).2.2

/-- For a fixed third counter the existence of a predecessor is independent
of the large even first counter. -/
theorem exact_row_gate {x y : Nat} (hy : 20 < y)
    (hx : 2*inverseBudget y≤ x) (heven : x%2=0) :
    (∀ a d, highLevelNext (.D a d)≠some (.D x y)) ↔
      Agent41DrainImageDecoder.blocked y := by
  constructor
  · intro hn
    have hl : leftCandidate x y= none := by
      cases hh : leftCandidate x y with
      | none => rfl
      | some p =>
        exact False.elim (hn p.1 p.2 (leftCandidate_sound hy hx heven (by simpa using hh)).2.2)
    have hr : rightCandidate x y= none := by
      cases hh : rightCandidate x y with
      | none => rfl
      | some p =>
        exact False.elim (hn p.1 p.2 (rightCandidate_sound hy hx heven (by simpa using hh)).2.2)
    unfold leftCandidate at hl
    unfold rightCandidate at hr
    unfold Agent41DrainImageDecoder.blocked
    by_cases h : y%2=0
    · rw [if_pos h] at hl hr ⊢
      constructor
      · cases hh : Agent41DrainImageDecoder.inverse (y-2) with
        | none => rfl
        | some b => simp [hh] at hl
      · cases hh : Agent41DrainImageDecoder.inverse (y-3) with
        | none => rfl
        | some b => simp [hh] at hr
    · rw [if_neg h] at hl hr ⊢
      constructor
      · cases hh : Agent41DrainImageDecoder.inverse (y-5) with
        | none => rfl
        | some b => simp [hh] at hl
      · cases hh : Agent41DrainImageDecoder.inverse y with
        | none => rfl
        | some b => simp [hh] at hr
  · intro hb a d
    exact Agent41DrainImageSource.no_parent_of_blocked a d x y (by omega) hx hb

/-- Whenever both candidate branches exist they are genuinely distinct. -/
theorem candidates_distinct {x y a d : Nat} (hy : 20 < y)
    (hx : 2*inverseBudget y≤ x) (heven : x%2=0) :
    leftCandidate x y= some (a,d) → rightCandidate x y≠some (a,d) := by
  intro hl hr
  have h₁ := (leftCandidate_sound hy hx heven hl).2.1
  have h₂ := (rightCandidate_sound hy hx heven hr).2.1
  omega

#print axioms exact_parent_candidates
#print axioms exact_row_gate
#print axioms candidates_distinct

#print axioms inverse_hit
#print axioms leftCandidate_sound
#print axioms rightCandidate_sound
end BB6.Agent41ExactParentRays
