import Root119F1MarkerLifecycle

namespace BB6Root119

/-- Exact inverse transition classification for entry into state A. -/
theorem to_A_exact_parent {u v : Conf} (hstep : next u = some v) (hA : v.q = .A) :
    (u.q = .E ∧ u.tape u.h = false ∧ v.h = u.h+1 ∧
      v.tape (v.h-1) = true) ∨
    (u.q = .E ∧ u.tape u.h = true ∧ v.h = u.h-1 ∧
      v.tape (v.h+1) = true) := by
  cases u with
  | mk q h t =>
      cases q <;> cases hb : t h <;> simp [next,hb] at hstep
      all_goals cases hstep
      all_goals simp_all [setBit]

/-- The exact A/0 transition, including its unique tape write. -/
theorem next_A_zero_shape (a : Conf) (hA : a.q = .A)
    (hzero : a.tape a.h = false) :
    next a = some ⟨.B,a.h+1,setBit a.tape a.h true⟩ := by
  cases a with
  | mk q h t =>
      change q = .A at hA
      subst q
      change t h = false at hzero
      simp [next,hzero]

/-- The exact F/0 transition, including its unique tape write. -/
theorem next_F_zero_shape (f : Conf) (hF : f.q = .F)
    (hzero : f.tape f.h = false) :
    next f = some ⟨.B,f.h-1,setBit f.tape f.h true⟩ := by
  cases f with
  | mk q h t =>
      change q = .F at hF
      subst q
      change t h = false at hzero
      simp [next,hzero]

/-- Every noninitial reached B/0 in the 10x left-context sector has an
    immediate F/0 predecessor one cell to its right. The only alternative
    B predecessor, A/0, is excluded by tracing the A state one step farther
    back: its E predecessor would force either the second-left cell or the
    current cell to be 1. The initial blank-to-B/0 transition is excluded by
    the third-left 1 hypothesis. -/
theorem reached_B0_left10_parent (c : Conf) (hc : Reach c)
    (hB : c.q = .B) (hcurrent : c.tape c.h = false)
    (hleft3 : c.tape (c.h-3) = true)
    (hleft2 : c.tape (c.h-2) = false) :
    ∃ f, Reach f ∧ f.q = .F ∧ f.tape f.h = false ∧
      f.h = c.h+1 ∧ next f = some c := by
  cases hc with
  | initial =>
      simp [blank] at hB
  | @follow u _ hu hstep =>
      rcases to_B hstep hB with hA | hF
      · rcases hA with ⟨hAq,hAread,hpos,hwrite⟩
        have hCshape : c =
            ⟨.B,u.h+1,setBit u.tape u.h true⟩ := by
          rw [next_A_zero_shape u hAq hAread] at hstep
          cases hstep
          rfl
        cases hu with
        | initial =>
            have hfalse : c.tape (c.h-3) = false := by
              rw [hCshape]
              change setBit blank.tape blank.h true (blank.h+1-3) = false
              simp [blank,setBit]
            rw [hleft3] at hfalse
            cases hfalse
        | @follow p _ hp hprev =>
            rcases to_A_exact_parent hprev hAq with hE0 | hE1
            · rcases hE0 with ⟨hEq,hreadE,hposE,hwriteE⟩
              have hcoord : u.h+1-2 = u.h-1 := by omega
              have htrue : c.tape (c.h-2) = true := by
                rw [hCshape]
                change setBit u.tape u.h true (u.h+1-2) = true
                rw [hcoord]
                exact (setBit_apply_ne u.tape u.h (u.h-1) true (by omega)).trans hwriteE
              rw [hleft2] at htrue
              cases htrue
            · rcases hE1 with ⟨hEq,hreadE,hposE,hwriteE⟩
              have htrue : c.tape c.h = true := by
                rw [hCshape]
                change setBit u.tape u.h true (u.h+1) = true
                exact (setBit_apply_ne u.tape u.h (u.h+1) true (by omega)).trans hwriteE
              rw [hcurrent] at htrue
              cases htrue
      · rcases hF with ⟨hFq,hFread,hpos,hwrite⟩
        refine ⟨u,hu,hFq,hFread,?_,hstep⟩
        omega

 /-- Every reached F/0 has exactly two possible backward shapes:
    either D/1 immediately to its left, or F/0 two cells to its right with
    the intervening B/1. The A/0 branch is impossible because its write
    would make the target F cell read 1. -/
theorem reached_F0_parent_split (c : Conf) (hc : Reach c)
    (hF : c.q = .F) (hcurrent : c.tape c.h = false) :
    (∃ d, Reach d ∧ d.q = .D ∧ d.tape d.h = true ∧
      d.h = c.h-1 ∧ next d = some c) ∨
    (∃ f b, Reach f ∧ f.q = .F ∧ f.tape f.h = false ∧
      f.h = c.h+2 ∧
      Reach b ∧ b.q = .B ∧ b.tape b.h = true ∧
      b.h = c.h+1 ∧ next f = some b ∧ next b = some c) := by
  cases hc with
  | initial =>
      simp [blank] at hF
  | @follow u _ hu hstep =>
      rcases to_F hstep hF with hB | hD
      · rcases hB with ⟨hBq,hbit,hpos⟩
        cases hu with
        | initial =>
            simp [blank] at hBq
        | @follow a _ ha hstepA =>
            rcases to_B hstepA hBq with hA | hF0
            · rcases hA with ⟨hAq,hzero,hposA,hwriteA⟩
              have hCshape : c =
                  ⟨.F,u.h-1,setBit u.tape u.h true⟩ := by
                rw [next_B_one u hBq hbit] at hstep
                cases hstep
                rfl
              have htrue : c.tape c.h = true := by
                rw [hCshape]
                change setBit u.tape u.h true (u.h-1) = true
                exact (setBit_apply_ne u.tape u.h (u.h-1) true (by omega)).trans hwriteA
              rw [hcurrent] at htrue
              cases htrue
            · rcases hF0 with ⟨hFq,hzero,hposF,hwriteF⟩
              refine Or.inr ⟨a,ha,hFq,hzero,?_,
                u,Reach.follow ha hstepA,hBq,hbit,?_,hstepA,hstep⟩
              · omega
              · omega
      · rcases hD with ⟨hDq,hbit,hpos,hwritten⟩
        exact Or.inl ⟨u,hu,hDq,hbit,by omega,hstep⟩

/-- A reached F/0 whose left neighbor is zero has a forced two-step
    predecessor cone: F/0 at h+2 -> B/1 at h+1 -> F/0 at h. The A/0
    alternative would write 1 at the target F head, contradicting F/0. -/
theorem reached_F0_left_zero_two_step_parent (c : Conf) (hc : Reach c)
    (hF : c.q = .F) (hcurrent : c.tape c.h = false)
    (hleft : c.tape (c.h-1) = false) :
    ∃ f, Reach f ∧ f.q = .F ∧ f.tape f.h = false ∧
      f.h = c.h+2 ∧
      ∃ b, Reach b ∧ b.q = .B ∧ b.tape b.h = true ∧
        b.h = c.h+1 ∧ next f = some b ∧ next b = some c := by
  obtain ⟨b,hb,hB,hbit,hpos,hstepB⟩ :=
    reached_F_left_zero_parent c hc hF hleft
  cases hb with
  | initial =>
      simp [blank] at hB
  | @follow a _ ha hstepA =>
      rcases to_B hstepA hB with hA | hF0
      · rcases hA with ⟨hAq,hzero,hposA,hwriteA⟩
        have hCshape : c =
            ⟨.F,b.h-1,setBit b.tape b.h true⟩ := by
          rw [next_B_one b hB hbit] at hstepB
          cases hstepB
          rfl
        have htrue : c.tape c.h = true := by
          rw [hCshape]
          change setBit b.tape b.h true (b.h-1) = true
          exact (setBit_apply_ne b.tape b.h (b.h-1) true (by omega)).trans hwriteA
        rw [hcurrent] at htrue
        cases htrue
      · rcases hF0 with ⟨hFq,hFzero,hposF,hwriteF⟩
        refine ⟨a,ha,hFq,hFzero,?_,
          ⟨b,Reach.follow ha hstepA,hB,hbit,hpos,hstepA,hstepB⟩⟩
        omega

/-- Combining the two inverse cones: every reached B/0 with left suffix
    10 (at h-3,h-2) and a zero under the head has the exact three-transition
    ancestry F/0(h+3) -> B/1(h+2) -> F/0(h+1) -> B/0(h). This is a
    source-level reachability theorem, not a finite-trace observation. -/
theorem reached_B0_left10_three_step_parent (c : Conf) (hc : Reach c)
    (hB : c.q = .B) (hcurrent : c.tape c.h = false)
    (hleft3 : c.tape (c.h-3) = true)
    (hleft2 : c.tape (c.h-2) = false) :
    ∃ f b g,
      Reach f ∧ f.q = .F ∧ f.tape f.h = false ∧ f.h = c.h+3 ∧
      Reach b ∧ b.q = .B ∧ b.tape b.h = true ∧ b.h = c.h+2 ∧
      Reach g ∧ g.q = .F ∧ g.tape g.h = false ∧ g.h = c.h+1 ∧
      next f = some b ∧ next b = some g ∧ next g = some c := by
  obtain ⟨g,hg,hG,hGzero,hGpos,hGstep⟩ :=
    reached_B0_left10_parent c hc hB hcurrent hleft3 hleft2
  have hGshape : c = ⟨.B,g.h-1,setBit g.tape g.h true⟩ := by
    rw [next_F_zero_shape g hG hGzero] at hGstep
    cases hGstep
    rfl
  have hGleft : g.tape (g.h-1) = false := by
    have hcell : c.tape c.h = g.tape (g.h-1) := by
      rw [hGshape]
      change setBit g.tape g.h true (g.h-1) = g.tape (g.h-1)
      exact setBit_apply_ne g.tape g.h (g.h-1) true (by omega)
    rw [hcurrent] at hcell
    exact hcell.symm
  obtain ⟨f,hf,hF,hFzero,hFpos,b,hb,hB1,hbit,hBpos,hFstep,hBstep⟩ :=
    reached_F0_left_zero_two_step_parent g hg hG hGzero hGleft
  refine ⟨f,b,g,hf,hF,hFzero,?_,
    hb,hB1,hbit,?_,
    hg,hG,hGzero,hGpos,hFstep,hBstep,hGstep⟩
  · rw [hGpos] at hFpos
    omega
  · rw [hGpos] at hBpos
    omega

#print axioms BB6Root119.to_A_exact_parent
#print axioms BB6Root119.reached_B0_left10_parent
#print axioms BB6Root119.reached_F0_parent_split
#print axioms BB6Root119.reached_F0_left_zero_two_step_parent
#print axioms BB6Root119.reached_B0_left10_three_step_parent

end BB6Root119
