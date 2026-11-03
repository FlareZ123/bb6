import RawBoundaryPhysicalQuotient

namespace BB6.RawBoundaryBridge
open BB6.Portfolio

/-- The physical coordinate immediately past the finite right suffix. -/
def rightEdge (c : CryptidBoundary.Cfg) (p : Int) : Int :=
  p + (c.r.length : Int)

private theorem frozen_step (c : CryptidBoundary.Cfg)
    (h : 6 ≤ c.st) : CryptidBoundary.step c = c := by
  rcases c with ⟨l,b,r,st⟩
  change 6 ≤ st at h
  rcases st with _ | _ | _ | _ | _ | _ | st
  all_goals try omega
  rfl

private theorem frozen_run (n : Nat) (c : CryptidBoundary.Cfg)
    (h : 6 ≤ c.st) : CryptidBoundary.run n c = c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [show CryptidBoundary.run (n+1) c =
      CryptidBoundary.run n (CryptidBoundary.step c) from rfl,
      frozen_step c h]
    exact ih c h

/-- In a live raw step the rightmost allocated physical cell cannot retreat. -/
theorem rightEdge_step (c : CryptidBoundary.Cfg) (p : Int)
    (h : (CryptidBoundary.step c).st < 6) :
    rightEdge c p ≤ rightEdge (CryptidBoundary.step c)
      (nextPos c p) := by
  rcases c with ⟨l,b,r,st⟩
  rcases st with _ | _ | _ | _ | _ | _ | st
  all_goals try (simp [CryptidBoundary.step] at h; omega)
  all_goals cases b <;> cases r <;> cases l <;>
    simp [rightEdge, nextPos, CryptidBoundary.step,
      CryptidBoundary.goL, CryptidBoundary.goR] at * <;> omega

/-- A run ending in a live state never included posthalt phantom head moves,
    so rightmost physical allocation is monotone throughout the actual run. -/
theorem rightEdge_run (n : Nat) (c : CryptidBoundary.Cfg) (p : Int)
    (h : (CryptidBoundary.run n c).st < 6) :
    rightEdge c p ≤ rightEdge (CryptidBoundary.run n c)
      (posAfter n c p) := by
  induction n generalizing c p with
  | zero => simp [CryptidBoundary.run, posAfter]
  | succ n ih =>
    have hs : (CryptidBoundary.step c).st < 6 := by
      by_cases hf : (CryptidBoundary.step c).st < 6
      · exact hf
      · have hg : 6 ≤ (CryptidBoundary.step c).st := by omega
        have he := frozen_run n (CryptidBoundary.step c) hg
        change (CryptidBoundary.run n (CryptidBoundary.step c)).st < 6 at h
        rw [he] at h
        omega
    have hp := rightEdge_step c p hs
    change (CryptidBoundary.run n (CryptidBoundary.step c)).st < 6 at h
    have ht := ih (CryptidBoundary.step c) (nextPos c p) h
    change rightEdge c p ≤ rightEdge (CryptidBoundary.run n (CryptidBoundary.step c))
      (posAfter n (CryptidBoundary.step c) (nextPos c p))
    omega

/-- Certified uniform lower bound on the actual raw physical F-head
    location at the exact all-k B-return; exact equality remains open. -/
theorem raw_full_B_head_lower (k : Nat) :
    ∃ p : Int,
      BB6.Portfolio.run D0 (12*k*k+49*k+40)
          (some (BB6.Portfolio.F0Pure (3*k+2) 0)) =
        some (BB6.Portfolio.F0Pure (8*k+9) p) ∧
      -(5*(k:Int)+6) ≤ p := by
  let c : CryptidBoundary.Cfg :=
    CryptidBoundary.init (List.replicate (3*k) true ++ [false])
  let t := 12*k*k+49*k+40
  have hstart : pack (unary (3*k+2)) 0 = pack c 0 := by
    rw [unary_eq_init_replicate (3*k)]
    change pack ⟨[],false,true::true::List.replicate (3*k) true,5⟩ 0 =
      pack ⟨[],false,(true::true::List.replicate (3*k) true)++[false],5⟩ 0
    exact (pack_right_append_zero [] _ false 5 0).symm
  have hreturn : CryptidBoundary.run t c = unary (8*k+9) := by
    simpa [t,c,unary] using (CryptidBoundary.full_B k [])
  let p := posAfter t c 0
  refine ⟨p, ?_, ?_⟩
  · calc
      BB6.Portfolio.run D0 t
          (some (BB6.Portfolio.F0Pure (3*k+2) 0)) =
          pack (CryptidBoundary.run t (unary (3*k+2)))
            (posAfter t (unary (3*k+2)) 0) := by
              rw [←pack_unary, run_pack]
      _ = pack (CryptidBoundary.run t c) p :=
        physical_run_congruence _ _ 0 0 hstart t
      _ = some (BB6.Portfolio.F0Pure (8*k+9) p) := by
        rw [hreturn, pack_unary]
  · have hlive : (CryptidBoundary.run t c).st < 6 := by
      rw [hreturn]
      simp [unary]
    have hb := rightEdge_run t c 0 hlive
    have hstartedge : rightEdge c 0 = ((3*k+3:Nat):Int) := by
      simp [rightEdge,c,CryptidBoundary.init]
      omega
    have hend : rightEdge (CryptidBoundary.run t c) p =
        p + ((8*k+9:Nat):Int) := by
      rw [hreturn]
      simp [rightEdge,unary]
    rw [hstartedge,hend] at hb
    omega

#print axioms rightEdge_run
#print axioms raw_full_B_head_lower
end BB6.RawBoundaryBridge
