import AffineConeLowStop
import CThreeSixAllCriterion
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 4000000

namespace BB6.Agent13AffineCone
open BB6.Agent46

/-- Start the full inverse cone at the original four-step inverse
    rectangle, rather than assuming the first parent is unique.
    This covers both parities of z and every compatible high bounce. -/
def rectangleRay (z : Nat) : Ray :=
  ⟨⟨180*16384,180*payloadBase z+28⟩,⟨166*16384,166*payloadBase z+25⟩⟩

def rectangleExcluded (f z : Nat) : Bool := excluded f (rectangleRay z)

theorem rectangleExcluded_periodic (f z : Nat) :
    rectangleExcluded f z=rectangleExcluded f (z%8192) := by
  have hb : payloadBase z=payloadBase (z%8192) := by unfold payloadBase; omega
  simp only [rectangleExcluded,rectangleRay,hb]

theorem rectangleRay_eval (z u t : Nat) (hu : u=16384*t+payloadBase z) :
    (rectangleRay z).x.eval t=180*u+28 ∧ (rectangleRay z).y.eval t=166*u+25 := by
  rw [hu]
  simp only [rectangleRay,Linear.eval,Nat.mul_add,Nat.mul_assoc]

/-- Every accepting inverse tree excludes an entire stopping-index cylinder,
    for all natural z, including arbitrarily large odd z with many parents. -/
theorem rectangle_stop_excluded (f z m k : Nat)
    (hm : m=512*z+67) (hstop : k+3*m+4=2^(2*m+3))
    (h : rectangleExcluded f z=true) : ¬ BB6.Agent3.CReach 1 k := by
  obtain ⟨u,hk,hu⟩ := stopping_payload z m k hm hstop
  obtain ⟨t,ht⟩ := payload_representation z u hu
  obtain ⟨hx,hy⟩ := rectangleRay_eval z u t ht
  intro hr
  rw [hk] at hr
  have hR := BB6.Agent13One307.four_step_to_rectangle u hr
  exact (source_excluded f (rectangleRay z) h t) (by rw [hx,hy]; exact hR)

def lowAllowedAffine (m : Nat) : Prop :=
  BB6.Agent11SixAll.lowAllowed m ∧
  (m%512≠67 ∨ rectangleExcluded 20 (m/512)=false)

private theorem low_power_bound (m : Nat) : 3*m+4≤2^(2*m+3) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have he : 2*(m+1)+3=(2*m+3)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

/-- Exact original-source blank halting equivalence with a verified executable
    whole-predecessor-tree sieve. The high branch and all low parameters
    not covered by the checker remain unbounded. -/
theorem blank_halts_iff_affine :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, lowAllowedAffine m ∧
        BB6.Agent11SixForced.sixForcedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, BB6.Agent11SixAll.highAllowed j m ∧
        BB6.Agent11SixForced.sixForcedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent11SixAll.blank_halts_iff_six_both]
  constructor
  · rintro (⟨m,hprior,hroot⟩ | ⟨j,m,hprior,hroot⟩)
    · let k := 2^(2*m+3)-(3*m+4)
      have hr : BB6.Agent3.CReach 1 k :=
        (BB6.Agent11SixForced.sixForcedRootDecision_iff 1 k).mp hroot
      have hstop : k+3*m+4=2^(2*m+3) := by
        dsimp [k]
        have hb := Nat.sub_add_cancel (low_power_bound m)
        omega
      have hfilter : m%512≠67 ∨ rectangleExcluded 20 (m/512)=false := by
        by_cases hm : m%512=67
        · right
          let z := m/512
          have he : m=512*z+67 := by
            have hh := Nat.mod_add_div m 512
            dsimp [z]
            omega
          cases hc : rectangleExcluded 20 z with
          | false => rfl
          | true => exact False.elim ((rectangle_stop_excluded 20 z m k he hstop hc) hr)
        · exact Or.inl hm
      exact Or.inl ⟨m,⟨hprior,hfilter⟩,hroot⟩
    · exact Or.inr ⟨j,m,hprior,hroot⟩
  · rintro (⟨m,⟨hprior,_⟩,hroot⟩ | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl ⟨m,hprior,hroot⟩
    · exact Or.inr ⟨j,m,hprior,hroot⟩

/-- Explicit earlier added clauses, through the accepted 1583/4096 criterion.
    Used only in an interpreted overlap census, not as an axiom or premise. -/
def previousClauses : List (Nat × Nat) :=
  [(8192,6723),(32768,2627),(16384,12867),(65536,4675),(65536,10819),
   (262144,33347),(1048576,885315),(2097152,1802819),
   (131072,84547),(262144,53827),(524288,240195),(524288,444995),
   (524288,299587),(4096,1091),(8192,3651),(16384,12355),(32768,22595),
   (65536,8259),(65536,7235)]
def previousExcluded (z : Nat) : Bool :=
  previousClauses.any (fun p => (512*z+67)%p.1==p.2)
#eval ((List.range 8192).filter (rectangleExcluded 20)).length
#eval ((List.range 8192).filter previousExcluded).length
#eval ((List.range 8192).filter (fun z => previousExcluded z && !rectangleExcluded 20 z)).length
#eval ((List.range 8192).filter (fun z => rectangleExcluded 20 z && !previousExcluded z)).length

#print axioms rectangle_stop_excluded
#print axioms rectangleExcluded_periodic
#print axioms blank_halts_iff_affine
end BB6.Agent13AffineCone
