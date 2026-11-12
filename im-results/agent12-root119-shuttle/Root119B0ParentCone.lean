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



/-- A time-indexed version of Reach, used only to make backward descent
    well-founded. -/
inductive Root119ReachN : Nat → Conf → Prop where
  | zero : Root119ReachN 0 blank
  | step {n : Nat} {c d : Conf} :
      Root119ReachN n c → next c = some d → Root119ReachN (n+1) d

theorem reach_has_steps {c : Conf} (hc : Reach c) :
    ∃ n, Root119ReachN n c := by
  induction hc with
  | initial =>
      exact ⟨0,Root119ReachN.zero⟩
  | @follow u v hu hstep ih =>
      rcases ih with ⟨n,hn⟩
      exact ⟨n+1,Root119ReachN.step hn hstep⟩

theorem reach_of_steps {n : Nat} {c : Conf}
    (hc : Root119ReachN n c) : Reach c := by
  induction hc with
  | zero =>
      exact Reach.initial
  | step hprev hstep ih =>
      exact Reach.follow ih hstep

/-- Exact finite transition paths, with their lengths retained in the type. -/
inductive Root119Path : Nat → Conf → Conf → Prop where
  | refl (c : Conf) : Root119Path 0 c c
  | step {n : Nat} {c d e : Conf} :
      next c = some d → Root119Path n d e → Root119Path (n+1) c e

theorem root119Path_comp {n m : Nat} {a b c : Conf}
    (h1 : Root119Path n a b) (h2 : Root119Path m b c) :
    Root119Path (n+m) a c := by
  induction h1 generalizing m c with
  | refl =>
      simpa using h2
  | @step n a d b hstep hpath ih =>
      have htail : Root119Path (n+m) d c := ih h2
      have hcomp : Root119Path ((n+m)+1) a c :=
        Root119Path.step hstep htail
      have hlen : (n+1)+m = (n+m)+1 := by omega
      simpa [hlen] using hcomp

 /-- Exact inverse transition classification for entry into D. -/
theorem to_D_exact_parent {u v : Conf} (hstep : next u = some v)
    (hD : v.q = .D) :
    (u.q = .C ∧ u.tape u.h = false ∧ v.h = u.h-1 ∧
      v.tape (v.h+1) = true) ∨
    (u.q = .F ∧ u.tape u.h = true ∧ v.h = u.h+1 ∧
      v.tape (v.h-1) = false) := by
  cases u with
  | mk q h t =>
      cases q <;> cases hb : t h <;> simp [next,hb] at hstep
      all_goals cases hstep
      all_goals simp_all [setBit]

/-- The exact D/1 transition, including its unique tape write. -/
theorem next_D_one_shape (d : Conf) (hD : d.q = .D)
    (hbit : d.tape d.h = true) :
    next d = some ⟨.F,d.h+1,setBit d.tape d.h true⟩ := by
  cases d with
  | mk q h t =>
      change q = .D at hD
      subst q
      change t h = true at hbit
      simp [next,hbit]

/-- A D/1 whose successor is F/0 must itself have an F/1 predecessor.
    The other possible D predecessor, C/0, writes 1 into the cell that the
    successor F/0 reads, so it is impossible. -/
theorem reached_D1_F0_successor_F1_parent (d e : Conf)
    (hd : Reach d) (hD : d.q = .D) (hbit : d.tape d.h = true)
    (hstep : next d = some e) (hF : e.q = .F)
    (hzero : e.tape e.h = false) :
    ∃ f, Reach f ∧ f.q = .F ∧ f.tape f.h = true ∧
      f.h = d.h-1 ∧ next f = some d := by
  cases hd with
  | initial =>
      simp [blank] at hD
  | @follow f _ hf hstepF =>
      rcases to_D_exact_parent hstepF hD with hC | hFparent
      · rcases hC with ⟨hCq,hCzero,hpos,hwrite⟩
        have hEshape : e =
            ⟨.F,d.h+1,setBit d.tape d.h true⟩ := by
          rw [next_D_one_shape d hD hbit] at hstep
          cases hstep
          rfl
        have htrue : e.tape e.h = true := by
          rw [hEshape]
          change setBit d.tape d.h true (d.h+1) = true
          exact (setBit_apply_ne d.tape d.h (d.h+1) true (by omega)).trans hwrite
        rw [hzero] at htrue
        cases htrue
      · rcases hFparent with ⟨hFq,hFbit,hpos,hwrite⟩
        refine ⟨f,hf,hFq,hFbit,?_,hstepF⟩
        omega

/-- Every reached F/0 has a D/1 ancestor at offset 2k-1 and a particular
    F/0 successor of that D/1. The path from this F/0 successor to the
    original F/0 has exactly 2k transitions. The proof is well-founded
    descent on the exact number of transitions from blank: an F/0
    predecessor is either D/1 immediately to its left, or another F/0 two
    cells to the right through B/1. -/
theorem reached_F0_D1_successor_path (n : Nat) (c : Conf)
    (hc : Root119ReachN n c) (hF : c.q = .F)
    (hzero : c.tape c.h = false) :
    ∃ k d e, Reach d ∧ d.q = .D ∧ d.tape d.h = true ∧
      d.h = c.h + (2*k : Int) - 1 ∧
      e.q = .F ∧ e.tape e.h = false ∧ next d = some e ∧
      Root119Path (2*k) e c := by
  induction n using Nat.strong_induction_on generalizing c with
  | h n ih =>
      cases hc with
      | zero =>
          simp [blank] at hF
      | @step m u v hprev hstep =>
          rcases to_F hstep hF with hB | hD
          · rcases hB with ⟨hBq,hbit,hpos⟩
            cases hprev with
            | zero =>
                simp [blank] at hBq
            | @step m' a _ hprev2 hstepA =>
                rcases to_B hstepA hBq with hA | hF0
                · rcases hA with ⟨hAq,hAzero,hposA,hwriteA⟩
                  have hCshape : c =
                      ⟨.F,u.h-1,setBit u.tape u.h true⟩ := by
                    rw [next_B_one u hBq hbit] at hstep
                    cases hstep
                    rfl
                  have htrue : c.tape c.h = true := by
                    rw [hCshape]
                    change setBit u.tape u.h true (u.h-1) = true
                    exact (setBit_apply_ne u.tape u.h (u.h-1) true (by omega)).trans hwriteA
                  rw [hzero] at htrue
                  cases htrue
                · rcases hF0 with ⟨hFq,hFzero,hposF,hwriteF⟩
                  have hm_lt : m' < n := by omega
                  obtain ⟨k,d,e,hd,hDq,hDbit,hdpos,hEq,hEzero,hstepD,hpath⟩ :=
                    ih m' hm_lt a hprev2 hFq hFzero
                  have haPos : a.h = c.h+2 := by omega
                  have hpath2 : Root119Path 2 a c :=
                    Root119Path.step hstepA
                      (Root119Path.step hstep (Root119Path.refl c))
                  have hpathOut := root119Path_comp hpath hpath2
                  have hposOut : d.h = c.h + (2*(k+1) : Int) - 1 := by
                    rw [haPos] at hdpos
                    omega
                  have hlen : (2*k+2) = 2*(k+1) := by omega
                  exact ⟨k+1,d,e,hd,hDq,hDbit,hposOut,hEq,hEzero,hstepD,
                    by simpa [hlen] using hpathOut⟩
          · rcases hD with ⟨hDq,hbit,hpos,hwritten⟩
            refine ⟨0,u,c,reach_of_steps hprev,hDq,hbit,?_,hF,hzero,hstep,
              Root119Path.refl c⟩
            omega

/-- The weaker D/1 ancestry statement, retained as a convenient projection. -/
theorem reached_F0_D1_ancestor (n : Nat) (c : Conf)
    (hc : Root119ReachN n c) (hF : c.q = .F)
    (hzero : c.tape c.h = false) :
    ∃ k d, Reach d ∧ d.q = .D ∧ d.tape d.h = true ∧
      d.h = c.h + (2*k : Int) - 1 ∧
      Root119Path (2*k+1) d c := by
  obtain ⟨k,d,e,hd,hDq,hDbit,hdpos,hEq,hEzero,hstepD,hpath⟩ :=
    reached_F0_D1_successor_path n c hc hF hzero
  exact ⟨k,d,hd,hDq,hDbit,hdpos,Root119Path.step hstepD hpath⟩

/-- Every reached F/0 has a reached F/1 ancestor at offset 2k-2 and an
    exact path of 2k+2 transitions from that F/1 to the F/0. -/
theorem reached_F0_F1_ancestor (n : Nat) (c : Conf)
    (hc : Root119ReachN n c) (hF : c.q = .F)
    (hzero : c.tape c.h = false) :
    ∃ k f, Reach f ∧ f.q = .F ∧ f.tape f.h = true ∧
      f.h = c.h + (2*k : Int) - 2 ∧
      Root119Path (2*k+2) f c := by
  obtain ⟨k,d,e,hd,hDq,hDbit,hdpos,hEq,hEzero,hstepD,hpath⟩ :=
    reached_F0_D1_successor_path n c hc hF hzero
  obtain ⟨f,hf,hF1,hFbit,hFpos,hstepF⟩ :=
    reached_D1_F0_successor_F1_parent d e hd hDq hDbit hstepD hEq hEzero
  have hpos : f.h = c.h + (2*k : Int) - 2 := by
    rw [hdpos] at hFpos
    omega
  have hpath2 : Root119Path 2 f e :=
    Root119Path.step hstepF
      (Root119Path.step hstepD (Root119Path.refl e))
  have hpathOut := root119Path_comp hpath2 hpath
  have hlen : 2+2*k = 2*k+2 := by omega
  exact ⟨k,f,hf,hF1,hFbit,hpos,by simpa [hlen] using hpathOut⟩

/-- Every reached B/0 in the all-time 10x sector has a D/1 ancestor exactly
    2k cells to its right and a path of 2k+2 transitions from that D/1 to the
    B/0. This is obtained by adjoining the forced F/0 predecessor of the
    B/0 to the general F/0 ancestry theorem. -/
theorem reached_B0_left10_D1_ancestor (c : Conf) (hc : Reach c)
    (hB : c.q = .B) (hcurrent : c.tape c.h = false)
    (hleft3 : c.tape (c.h-3) = true)
    (hleft2 : c.tape (c.h-2) = false) :
    ∃ k d, Reach d ∧ d.q = .D ∧ d.tape d.h = true ∧
      d.h = c.h + (2*k : Int) ∧
      Root119Path (2*k+2) d c := by
  obtain ⟨g,hg,hG,hGzero,hGpos,hGstep⟩ :=
    reached_B0_left10_parent c hc hB hcurrent hleft3 hleft2
  obtain ⟨n,hn⟩ := reach_has_steps hg
  obtain ⟨k,d,hd,hDq,hDbit,hdpos,hpath⟩ :=
    reached_F0_D1_ancestor n g hn hG hGzero
  have hpos : d.h = c.h + (2*k : Int) := by
    rw [hGpos] at hdpos
    omega
  have hpath1 : Root119Path 1 g c :=
    Root119Path.step hGstep (Root119Path.refl c)
  have hpathOut := root119Path_comp hpath hpath1
  have hlen : (2*k+1)+1 = 2*k+2 := by omega
  exact ⟨k,d,hd,hDq,hDbit,hpos,by simpa [hlen] using hpathOut⟩

#print axioms BB6Root119.to_A_exact_parent
#print axioms BB6Root119.reached_B0_left10_parent
#print axioms BB6Root119.reached_F0_parent_split
#print axioms BB6Root119.reached_F0_left_zero_two_step_parent
#print axioms BB6Root119.reached_B0_left10_three_step_parent
#print axioms BB6Root119.reached_F0_D1_ancestor
#print axioms BB6Root119.reached_B0_left10_D1_ancestor

end BB6Root119
