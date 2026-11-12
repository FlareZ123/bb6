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

/-- Every reached F/0 has a D/1 ancestor at signed offset 2k-1 and a particular
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



/-- Every reached B/0 in the 10x sector has a reached F/1 ancestor at
    offset 2k-1 and an exact path of 2k+3 transitions from
    that F/1 to the B/0. Thus the backward chain is not merely known to end
    at D/1: its endpoint is forced to have an F/1 parent because the next
    state on the chain is F/0. -/
theorem reached_B0_left10_F1_ancestor (c : Conf) (hc : Reach c)
    (hB : c.q = .B) (hcurrent : c.tape c.h = false)
    (hleft3 : c.tape (c.h-3) = true)
    (hleft2 : c.tape (c.h-2) = false) :
    ∃ k f, Reach f ∧ f.q = .F ∧ f.tape f.h = true ∧
      f.h = c.h + (2*k : Int) - 1 ∧
      Root119Path (2*k+3) f c := by
  obtain ⟨g,hg,hG,hGzero,hGpos,hGstep⟩ :=
    reached_B0_left10_parent c hc hB hcurrent hleft3 hleft2
  obtain ⟨n,hn⟩ := reach_has_steps hg
  obtain ⟨k,f,hf,hF1,hFbit,hFpos,hpath⟩ :=
    reached_F0_F1_ancestor n g hn hG hGzero
  have hpos : f.h = c.h + (2*k : Int) - 1 := by
    rw [hGpos] at hFpos
    omega
  have hpath1 : Root119Path 1 g c :=
    Root119Path.step hGstep (Root119Path.refl c)
  have hpathOut := root119Path_comp hpath hpath1
  have hlen : (2*k+2)+1 = 2*k+3 := by omega
  exact ⟨k,f,hf,hF1,hFbit,hpos,by simpa [hlen] using hpathOut⟩



/-! ## Tight left-path extraction

A path whose length equals its net leftward displacement has no right-moving
step. This turns the ancestry path above into a tape-word theorem, rather than
merely an offset statement.
-/

theorem parentCone_next_head_lower (c d : Conf)
    (hs : next c = some d) : c.h-1 ≤ d.h := by
  rcases c with ⟨q,h,t⟩
  cases q <;> cases hb : t h <;> simp [next,hb] at hs
  all_goals cases hs
  all_goals omega

theorem parentCone_next_tape_away (c d : Conf)
    (hs : next c = some d) (x : Int) (hx : x ≠ c.h) :
    d.tape x = c.tape x := by
  rcases c with ⟨q,h,t⟩
  cases q <;> cases hb : t h <;> simp_all [next,setBit]

theorem parentCone_path_head_lower {n : Nat} {c d : Conf}
    (hp : Root119Path n c d) : c.h-(n:Int) ≤ d.h := by
  induction hp with
  | refl => simp
  | @step n c u d hs ht ih =>
      have hstep := parentCone_next_head_lower c u hs
      omega

/-- If a path has exactly its maximum possible leftward displacement, its
    first transition is leftward and the tail is tight as well. -/
theorem parentCone_path_tight_first {n : Nat} {c d : Conf}
    (hp : Root119Path (n+1) c d)
    (hdisp : d.h = c.h-((n+1:Nat):Int)) :
    ∃ u, next c = some u ∧ u.h=c.h-1 ∧
      Root119Path n u d ∧ d.h=u.h-(n:Int) := by
  cases hp with
  | @step n c u d hs ht =>
      have hstep := parentCone_next_head_lower c u hs
      have htail := parentCone_path_head_lower ht
      have hpos : u.h=c.h-1 := by omega
      have hdispTail : d.h=u.h-(n:Int) := by omega
      exact ⟨u,hs,hpos,ht,hdispTail⟩

def parentConeNoBF (q : Q) : Prop := q ≠ .B ∧ q ≠ .F

theorem parentCone_next_left_preserves_noBF (c d : Conf)
    (hc : parentConeNoBF c.q) (hs : next c = some d)
    (hpos : d.h=c.h-1) : parentConeNoBF d.q := by
  rcases c with ⟨q,h,t⟩
  cases q <;> cases hb : t h <;>
    simp_all [next,parentConeNoBF,hb] <;> omega

/-- A tight all-left path cannot enter B or F if it starts in C, D, E, or A. -/
theorem parentCone_path_left_preserves_noBF {n : Nat} {c d : Conf}
    (hp : Root119Path n c d)
    (hdisp : d.h=c.h-(n:Int))
    (hc : parentConeNoBF c.q) : parentConeNoBF d.q := by
  revert c d hp hdisp hc
  induction n with
  | zero =>
      intro c d hp hdisp hc
      cases hp
      exact hc
  | succ n ih =>
      intro c d hp hdisp hc
      obtain ⟨u,hs,hpos,ht,hdispTail⟩ :=
        parentCone_path_tight_first hp hdisp
      exact ih u d ht hdispTail
        (parentCone_next_left_preserves_noBF c u hc hs hpos)

/-- Along a tight leftward path, the final tape agrees with the initial tape
    at every cell at or left of the final head: none of those cells was
    visited by the head. -/
theorem parentCone_path_tight_preserves_tape {n : Nat} {c d : Conf}
    (hp : Root119Path n c d)
    (hdisp : d.h=c.h-(n:Int))
    (x : Int) (hx : x≤d.h) : d.tape x=c.tape x := by
  revert c d hp hdisp x hx
  induction n with
  | zero =>
      intro c d hp hdisp x hx
      cases hp
      rfl
  | succ n ih =>
      intro c d hp hdisp x hx
      obtain ⟨u,hs,hpos,ht,hdispTail⟩ :=
        parentCone_path_tight_first hp hdisp
      have haway : u.tape x=c.tape x :=
        parentCone_next_tape_away c u hs (by omega)
      have htail : d.tape x=u.tape x :=
        ih u d ht hdispTail x (by omega)
      exact htail.trans haway

/-- A tight path of 2k+1 left steps from F/0 to B/0 must read the alternating
    F/0,B/1 corridor at every pair. The endpoint B/0 rules out an intermediate
    B/0: its C successor can never return to B along an all-left path. -/
theorem parentCone_f0_b0_corridor (k : Nat) (c d : Conf)
    (hcF : c.q=.F) (hc0 : c.tape c.h=false)
    (hdB : d.q=.B) (hd0 : d.tape d.h=false)
    (hp : Root119Path (2*k+1) c d)
    (hdisp : d.h=c.h-((2*k+1:Nat):Int)) :
    ∀ i : Nat, i<k →
      c.tape (c.h-2*(i:Int))=false ∧
      c.tape (c.h-2*(i:Int)-1)=true := by
  revert c d hcF hc0 hdB hd0 hp hdisp
  induction k with
  | zero =>
      intro c d hcF hc0 hdB hd0 hp hdisp i hi
      omega
  | succ k ih =>
      intro c d hcF hc0 hdB hd0 hp hdisp i hi
      have hlen : 2*(k+1)+1=(2*k+2)+1 := by omega
      have hp' : Root119Path ((2*k+2)+1) c d := by
        simpa [hlen] using hp
      have hdisp' : d.h=c.h-((2*k+3:Nat):Int) := by
        simpa [hlen] using hdisp
      obtain ⟨b,hstep1,hbpos,hp1,hdisp1⟩ :=
        parentCone_path_tight_first hp' hdisp'
      rw [next_F_zero_shape c hcF hc0] at hstep1
      cases hstep1
      have hlen2 : 2*k+2=(2*k+1)+1 := by omega
      have hp1' : Root119Path ((2*k+1)+1) b d := by
        simpa [hlen2] using hp1
      obtain ⟨u,hstep2,hupos,hp2,hdisp2⟩ :=
        parentCone_path_tight_first hp1' hdisp1
      have hbBit : b.tape b.h=true := by
        by_contra hbNot
        have hbZero : b.tape b.h=false := by
          cases hbit : b.tape b.h <;> simp_all
        simp [next,hbZero] at hstep2
        cases hstep2
        have hno := parentCone_path_left_preserves_noBF hp2 hdisp2
          (by simp [parentConeNoBF])
        exact hno.1 hdB
      rw [next_B_one b rfl hbBit] at hstep2
      cases hstep2
      obtain ⟨v,hstep3,hvpos,hp3,hdisp3⟩ :=
        parentCone_path_tight_first hp2 hdisp2
      have huZero : u.tape u.h=false := by
        by_cases hu : u.tape u.h=false
        · exact hu
        · have huOne : u.tape u.h=true := by
            cases hbit : u.tape u.h <;> simp_all
          have hFone : next u =
              some ⟨.D,u.h+1,setBit u.tape u.h false⟩ := by
            simp [next,huOne]
          rw [hFone] at hstep3
          cases hstep3
          omega
      have hpat := ih u d rfl huZero hdB hd0 hp2 hdisp2
      by_cases hi0 : i=0
      · subst i
        have hbtape : b.tape b.h=c.tape (c.h-1) := by
          simp [setBit,show c.h-1 ≠ c.h by omega]
        exact ⟨hc0,hbtape.symm.trans hbBit⟩
      · have hi' : i-1<k := by omega
        have hpatt := hpat (i-1) hi'
        have hupos' : u.h=c.h-2 := by omega
        have huTape (x : Int) (hx : x≤c.h-2) : u.tape x=c.tape x := by
          calc
            u.tape x = b.tape x := by
              simp [setBit,show x ≠ b.h by rw [hbpos]; omega]
            _ = c.tape x := by
              simp [setBit,show x ≠ c.h by omega]
        have hidx1 : u.h-2*((i-1:Int))=c.h-2*(i:Int) := by
          rw [hupos']
          omega
        have hidx2 : u.h-2*((i-1:Int))-1=c.h-2*(i:Int)-1 := by
          rw [hupos']
          omega
        constructor
        · calc
            c.tape (c.h-2*(i:Int)) =
                u.tape (u.h-2*((i-1:Int))) := by
                  rw [hidx1]
                  symm
                  exact huTape _ (by rw [hidx1]; omega)
            _ = false := hpatt.1
        · calc
            c.tape (c.h-2*(i:Int)-1) =
                u.tape (u.h-2*((i-1:Int))-1) := by
                  rw [hidx2]
                  symm
                  exact huTape _ (by rw [hidx2]; omega)
            _ = true := hpatt.2




/-- Expose the D/1 and F/0 witnesses hidden by the shorter F/1 ancestry
    projection. The middle path is the exact leftward corridor to the B/0
    parent. -/
theorem reached_B0_left10_path_components (c : Conf) (hc : Reach c)
    (hB : c.q=.B) (hcurrent : c.tape c.h=false)
    (hleft3 : c.tape (c.h-3)=true)
    (hleft2 : c.tape (c.h-2)=false) :
    ∃ k f d e g,
      1≤k ∧ Reach f ∧ f.q=.F ∧ f.tape f.h=true ∧
        f.h=c.h+(2*k:Int)-1 ∧
      Reach d ∧ d.q=.D ∧ d.tape d.h=true ∧
        d.h=f.h+1 ∧ next f=some d ∧
      Reach e ∧ e.q=.F ∧ e.tape e.h=false ∧
        e.h=f.h+2 ∧ next d=some e ∧
      Reach g ∧ g.q=.F ∧ g.tape g.h=false ∧
        g.h=c.h+1 ∧ Root119Path (2*k) e g ∧ next g=some c := by
  obtain ⟨g,hg,hG,hGzero,hGpos,hGstep⟩ :=
    reached_B0_left10_parent c hc hB hcurrent hleft3 hleft2
  obtain ⟨n,hn⟩ := reach_has_steps hg
  obtain ⟨k,d,e,hd,hD,hDbit,hdpos,hE,hEzero,hstepD,hpath⟩ :=
    reached_F0_D1_successor_path n g hn hG hGzero
  obtain ⟨f,hf,hF,hFbit,hFpos,hstepF⟩ :=
    reached_D1_F0_successor_F1_parent d e hd hD hDbit hstepD hE hEzero
  have hposF : f.h=c.h+(2*k:Int)-1 := by
    rw [hGpos] at hdpos
    rw [hFpos]
    omega
  have hposD : d.h=f.h+1 := by omega
  have heReach : Reach e := Reach.follow hd hstepD
  have hDshape := next_D_one_shape d hD hDbit
  have heEq : e = ⟨.F,d.h+1,setBit d.tape d.h true⟩ := by
    have hsome : some e = some ⟨.F,d.h+1,setBit d.tape d.h true⟩ :=
      hstepD.symm.trans hDshape
    injection hsome with heq
    exact heq
  have hposE : e.h=f.h+2 := by
    rw [heEq,hposD]
    omega
  have hkpos : 1≤k := by
    by_contra hnot
    have hk0 : k=0 := by omega
    subst k
    have hdpos0 : d.h=c.h := by rw [hposF] at hposD; omega
    have hsome : some e = some ⟨.F,d.h+1,setBit d.tape d.h true⟩ :=
      hstepD.symm.trans hDshape
    have heq : e = ⟨.F,d.h+1,setBit d.tape d.h true⟩ := by
      injection hsome with heq
      exact heq
    cases hpath
    have hwrite : e.tape c.h=true := by
      rw [heq]
      simp [setBit,hdpos0]
    have hcopy : c.tape c.h=e.tape c.h :=
      parentCone_next_tape_away g c hGstep c.h (by rw [hGpos]; omega)
    rw [hcurrent] at hcopy
    rw [hwrite] at hcopy
    cases hcopy
  exact ⟨k,f,d,e,g,hkpos,hf,hF,hFbit,hposF,
    hd,hD,hDbit,hposD,hstepF,
    heReach,hE,hEzero,hposE,hstepD,
    hg,hG,hGzero,hGpos,hpath,hGstep⟩

/-- Every reached B/0 in the left-10 sector has an F/1 ancestor whose first
    two right cells are exactly 1,0. Moreover the tight ancestry path forces
    every later alternating retreat cell. For k≥2 these are precisely the
    n=0, m=k-2 hypotheses of odd_f1_retreat_to_b0. -/
theorem reached_B0_left10_odd_seed_conditions (c : Conf) (hc : Reach c)
    (hB : c.q=.B) (hcurrent : c.tape c.h=false)
    (hleft3 : c.tape (c.h-3)=true)
    (hleft2 : c.tape (c.h-2)=false) :
    ∃ k f,
      1≤k ∧ Reach f ∧ f.q=.F ∧ f.tape f.h=true ∧
      f.h=c.h+(2*k:Int)-1 ∧
      f.tape (f.h+1)=true ∧ f.tape (f.h+2)=false ∧
      (∀ i : Nat, i+2<k →
        f.tape (f.h-2-2*(i:Int))=false ∧
        f.tape (f.h-3-2*(i:Int))=true) ∧
      (2≤k →
        f.tape (f.h-1)=true ∧
        f.tape (f.h-2*(k:Int)+2)=false ∧
        f.tape (f.h-2*(k:Int)+1)=false) := by
  obtain ⟨k,f,d,e,g,hkpos,hf,hF,hFbit,hposF,hd,hD,hDbit,hposD,
    hstepF,he,hE,hEzero,hposE,hstepD,hg,hG,hGzero,hGpos,hpath,hGstep⟩ :=
      reached_B0_left10_path_components c hc hB hcurrent hleft3 hleft2
  have hpathGC : Root119Path 1 g c :=
    Root119Path.step hGstep (Root119Path.refl c)
  have hpathEC : Root119Path (2*k+1) e c := by
    simpa using root119Path_comp hpath hpathGC
  have hdispEC : c.h=e.h-((2*k+1:Nat):Int) := by
    rw [hposE,hposF]
    omega
  have hdispEG : g.h=e.h-(2*k:Int) := by
    rw [hposE,hposF,hGpos]
    omega
  have hpattern := parentCone_f0_b0_corridor k e c hE hEzero hB hcurrent
    hpathEC hdispEC
  have hEF (x : Int) (hxf : x≠f.h) (hxd : x≠d.h) :
      e.tape x=f.tape x :=
    (parentCone_next_tape_away d e hstepD x hxd).trans
      (parentCone_next_tape_away f d hstepF x hxf)
  have honesEq : d.tape (f.h+1)=f.tape (f.h+1) :=
    parentCone_next_tape_away f d hstepF (f.h+1) (by omega)
  have hDread : d.tape (f.h+1)=true := by
    simpa [hposD] using hDbit
  have hones : f.tape (f.h+1)=true := honesEq.symm.trans hDread
  have hzeroE : e.tape (f.h+2)=false := by
    simpa [hposE] using hEzero
  have hzeroEq : e.tape (f.h+2)=f.tape (f.h+2) :=
    hEF (f.h+2) (by omega) (by omega)
  have hzero : f.tape (f.h+2)=false := hzeroEq.symm.trans hzeroE
  have hfb : ∀ i : Nat, i+2<k →
      f.tape (f.h-2-2*(i:Int))=false ∧
      f.tape (f.h-3-2*(i:Int))=true := by
    intro i hi
    have hpatt := hpattern (i+2) (by omega)
    have hidx1 : e.h-2*((i+2:Int))=f.h-2-2*(i:Int) := by
      rw [hposE]
      omega
    have hidx2 : e.h-2*((i+2:Int))-1=f.h-3-2*(i:Int) := by
      rw [hposE]
      omega
    have he1 : e.tape (f.h-2-2*(i:Int))=false := by
      simpa [hidx1] using hpatt.1
    have he2 : e.tape (f.h-3-2*(i:Int))=true := by
      simpa [hidx2] using hpatt.2
    have heq1 := hEF (f.h-2-2*(i:Int)) (by omega) (by omega)
    have heq2 := hEF (f.h-3-2*(i:Int)) (by omega) (by omega)
    exact ⟨heq1.symm.trans he1,heq2.symm.trans he2⟩
  have hretreat : 2≤k →
      f.tape (f.h-1)=true ∧
      f.tape (f.h-2*(k:Int)+2)=false ∧
      f.tape (f.h-2*(k:Int)+1)=false := by
    intro hk2
    have hp1 := hpattern 1 (by omega)
    have hidxLeft : e.h-2*(1:Int)-1=f.h-1 := by
      rw [hposE]
      omega
    have heLeft : e.tape (f.h-1)=true := by
      simpa [hidxLeft] using hp1.2
    have heqLeft := hEF (f.h-1) (by omega) (by omega)
    have hleft : f.tape (f.h-1)=true := heqLeft.symm.trans heLeft
    have hpresG := parentCone_path_tight_preserves_tape
      hpath hdispEG g.h le_rfl
    have heG : e.tape g.h=false := hpresG.symm.trans hGzero
    have hidxF : f.h-2*(k:Int)+2=g.h := by
      rw [hposF,hGpos]
      omega
    have heqG := hEF g.h (by rw [hidxF]; omega) (by rw [hposD,hidxF]; omega)
    have hfinalF : f.tape (f.h-2*(k:Int)+2)=false := by
      simpa [hidxF] using heqG.symm.trans heG
    have hpresC := parentCone_path_tight_preserves_tape
      hpathEC hdispEC c.h le_rfl
    have heC : e.tape c.h=false := hpresC.symm.trans hcurrent
    have hidxB : f.h-2*(k:Int)+1=c.h := by
      rw [hposF]
      omega
    have heqC := hEF c.h (by rw [hidxB]; omega) (by rw [hposD,hidxB]; omega)
    have hfinalB : f.tape (f.h-2*(k:Int)+1)=false := by
      simpa [hidxB] using heqC.symm.trans heC
    exact ⟨hleft,hfinalF,hfinalB⟩
  exact ⟨k,f,hkpos,hf,hF,hFbit,hposF,hones,hzero,hfb,hretreat⟩




/-- The complete half-line at and left of a reached left-10 B/0 target is
    identical to that of its F/1 ancestor. The two rightward prefix writes
    lie strictly to the right of the target; the remaining path is tight and
    leftward, so it never writes at or left of the target head. -/
theorem reached_B0_left10_left_tape_agreement (c : Conf) (hc : Reach c)
    (hB : c.q=.B) (hcurrent : c.tape c.h=false)
    (hleft3 : c.tape (c.h-3)=true)
    (hleft2 : c.tape (c.h-2)=false) :
    ∃ k f,
      1≤k ∧ Reach f ∧ f.q=.F ∧ f.tape f.h=true ∧
      f.h=c.h+(2*k:Int)-1 ∧
      ∀ x : Int, x≤c.h → c.tape x=f.tape x := by
  obtain ⟨k,f,d,e,g,hkpos,hf,hF,hFbit,hposF,hd,hD,hDbit,hposD,
    hstepF,he,hE,hEzero,hposE,hstepD,hg,hG,hGzero,hGpos,hpath,hGstep⟩ :=
      reached_B0_left10_path_components c hc hB hcurrent hleft3 hleft2
  have hpathGC : Root119Path 1 g c :=
    Root119Path.step hGstep (Root119Path.refl c)
  have hpathEC : Root119Path (2*k+1) e c := by
    simpa using root119Path_comp hpath hpathGC
  have hdispEC : c.h=e.h-((2*k+1:Nat):Int) := by
    rw [hposE,hposF]
    omega
  have hEF (x : Int) (hxf : x≠f.h) (hxd : x≠d.h) :
      e.tape x=f.tape x :=
    (parentCone_next_tape_away d e hstepD x hxd).trans
      (parentCone_next_tape_away f d hstepF x hxf)
  refine ⟨k,f,hkpos,hf,hF,hFbit,hposF,?_⟩
  intro x hx
  have hpres := parentCone_path_tight_preserves_tape
    hpathEC hdispEC x hx
  have hEFx := hEF x (by omega) (by omega)
  exact hpres.trans hEFx


#print axioms BB6Root119.to_A_exact_parent
#print axioms BB6Root119.to_D_exact_parent
#print axioms BB6Root119.reached_D1_F0_successor_F1_parent
#print axioms BB6Root119.reached_F0_D1_successor_path
#print axioms BB6Root119.reached_F0_F1_ancestor
#print axioms BB6Root119.reached_B0_left10_parent
#print axioms BB6Root119.reached_F0_parent_split
#print axioms BB6Root119.reached_F0_left_zero_two_step_parent
#print axioms BB6Root119.reached_B0_left10_three_step_parent
#print axioms BB6Root119.reached_F0_D1_ancestor
#print axioms BB6Root119.reached_B0_left10_D1_ancestor
#print axioms BB6Root119.reached_B0_left10_F1_ancestor
#print axioms BB6Root119.parentCone_f0_b0_corridor
#print axioms BB6Root119.reached_B0_left10_path_components
#print axioms BB6Root119.reached_B0_left10_odd_seed_conditions
#print axioms BB6Root119.reached_B0_left10_left_tape_agreement

end BB6Root119
