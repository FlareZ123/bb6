import RestartWallSource
import Mod7SlackLeaf

set_option maxRecDepth 8192

namespace BB6.Agent9RestartWallLowTrace

open BB6.Agent9RestartWallSource
open BB6.Agent9RestartWallTelescoping
open BB6.Agent9Mod7Slack

/-- The affine energy used by the mod-7 low-suffix leaf, expressed at an
    authentic restart state with absolute restart counter c and relative
    accumulated cost s. -/
def restartEnergy (P c s x : Nat) : Int :=
  98 * (P : Int) - 49 * (x : Int) - 14 * (c+s+6 : Int) + 90

/-- The shifted source offset paired with restartEnergy. -/
def restartOffset (c s : Nat) : Int := (c+s+6 : Int)

/-- One exact source RestartWalk edge of cost 1, 2, or 3 is precisely the
    corresponding scalar LowStep.  Here the RestartWalk cost e is t+1,
    where t is the original inverse depth. -/
theorem restartStep_lowStep
    (P c s x e x' : Nat)
    (hstep : x + 14*P = 2^e*x' + 2*(c+3+s))
    (he : 1 ≤ e) (hle : e ≤ 3) :
    LowStep (P : Int)
      (restartEnergy P c s x) (restartOffset c s)
      (restartEnergy P c (s+e) x') (restartOffset c (s+e)) := by
  have hcases : e=1 ∨ e=2 ∨ e=3 := by omega
  rcases hcases with h1 | h2 | h3
  · subst e
    have hstep' : x + 14*P = 2*x' + 2*(c+3+s) := by
      simpa using hstep
    have hstepI : (x : Int) + 14*(P : Int) =
        2*(x' : Int) + 2*((c : Int)+3+(s : Int)) := by
      exact_mod_cast hstep'
    refine Or.inl ⟨?_, ?_⟩
    · simp [restartOffset]
      omega
    · simp [restartEnergy, restartOffset]
      omega
  · subst e
    have hstep' : x + 14*P = 4*x' + 2*(c+3+s) := by
      simpa using hstep
    have hstepI : (x : Int) + 14*(P : Int) =
        4*(x' : Int) + 2*((c : Int)+3+(s : Int)) := by
      exact_mod_cast hstep'
    refine Or.inr (Or.inl ⟨?_, ?_⟩)
    · simp [restartOffset]
      omega
    · simp [restartEnergy, restartOffset]
      omega
  · subst e
    have hstep' : x + 14*P = 8*x' + 2*(c+3+s) := by
      simpa using hstep
    have hstepI : (x : Int) + 14*(P : Int) =
        8*(x' : Int) + 2*((c : Int)+3+(s : Int)) := by
      exact_mod_cast hstep'
    refine Or.inr (Or.inr ⟨?_, ?_⟩)
    · simp [restartOffset]
      omega
    · simp [restartEnergy, restartOffset]
      omega

/-- Every authentic RestartWalk whose recorded costs are in {1,2,3}
    induces a LowTrace with exactly the same endpoints and offsets. -/
theorem restartWalk_toLowTrace
    (P c x s xend : Nat) (es : List Nat)
    (hwalk : RestartWalk P c x s es xend)
    (hpos : ∀ e, e ∈ es → 1 ≤ e)
    (hlow : ∀ e, e ∈ es → e ≤ 3) :
    LowTrace (P : Int)
      (restartEnergy P c s x) (restartOffset c s)
      (restartEnergy P c (s+totalCost es) xend)
      (restartOffset c (s+totalCost es)) := by
  induction hwalk generalizing hpos hlow with
  | nil x s =>
      exact LowTrace.refl _ _
  | @cons x s e es x' xend hstep hrest ih =>
      have hepos : 1 ≤ e := hpos e (by simp)
      have helow : e ≤ 3 := hlow e (by simp)
      have hposTail : ∀ f, f ∈ es → 1 ≤ f := by
        intro f hf
        exact hpos f (by simp [hf])
      have hlowTail : ∀ f, f ∈ es → f ≤ 3 := by
        intro f hf
        exact hlow f (by simp [hf])
      have hfirst := restartStep_lowStep P c s x e x' hstep hepos helow
      have htail := ih hposTail hlowTail
      simpa [totalCost, Nat.add_assoc] using
        (LowTrace.step hfirst htail)

/-- The source-authentic suffix after the most recent depth-at-least-three
    edge is therefore a genuine scalar LowTrace, not merely a recurrence
    guessed from its endpoints. -/
theorem restartPath_toLowTrace
    (n b d m : Nat) (path : RestartPath n b d m) :
    LowTrace ((2^n : Nat) : Int)
      (restartEnergy (2^n) path.c 0 path.x0)
      (restartOffset path.c 0)
      (restartEnergy (2^n) path.c path.L (d-1))
      (restartOffset path.c path.L) := by
  have h := restartWalk_toLowTrace
    (2^n) path.c path.x0 0 (d-1) path.es
    path.walk path.hPos path.hLow
  simpa [path.hTotal] using h

/-- At a wall endpoint, the final scalar energy is exactly the wall energy
    used by Mod7SlackLeaf. -/
theorem restartPath_wall_energy
    (n b d m : Nat) (path : RestartPath n b d m)
    (hmass : b+d+2*m+2*n+13=14*2^n)
    (hwall : b+4*m+4*n+20=12*2^n) :
    restartEnergy (2^n) path.c path.L (d-1) =
      -112 * restartOffset path.c path.L + 384 := by
  have hd := source_wall_endpoint (2^n) n b d m hmass hwall
  have hD : d-1 = 2*2^n + 2*(path.c+path.L) + 6 := by
    rw [hd]
    have hBase := path.hBase
    have hCost := path.hCost
    omega
  have hDI : ((d-1 : Nat) : Int) =
      2*(2^n : Int) + 2*((path.c+path.L : Nat) : Int) + 6 := by
    exact_mod_cast hD
  unfold restartEnergy restartOffset
  rw [hDI]
  simp
  omega

/-- The initial restart energy is always 6 modulo 7.  This is the
    source-coordinate origin of the finite mod-7 candidate list. -/
theorem restartPath_initial_mod7
    (n b d m : Nat) (path : RestartPath n b d m) :
    restartEnergy (2^n) path.c 0 path.x0 % 7 = 6 := by
  unfold restartEnergy
  omega

/-- The initial restart energy is strictly below 98P, without requiring
    its separate positivity hypothesis. -/
theorem restartPath_initial_upper
    (n b d m : Nat) (hn : 1 ≤ n) (path : RestartPath n b d m) :
    restartEnergy (2^n) path.c 0 path.x0 < 98*(2^n : Int) := by
  have hc : 1 ≤ path.c := by
    rw [path.hBase]
    omega
  simp [restartEnergy]
  omega

/-- A prefix consisting entirely of depth-two inverse edges scales the
    restart energy by exactly 8 per edge. -/
theorem restartWalk_all_three_energy_scale
    (P c x s xend : Nat) (es : List Nat)
    (hwalk : RestartWalk P c x s es xend)
    (hall : ∀ e, e ∈ es → e=3) :
    restartEnergy P c s x =
      (8 : Int)^es.length *
        restartEnergy P c (s+totalCost es) xend := by
  induction hwalk generalizing hall with
  | nil x s =>
      simp [restartEnergy, totalCost]
  | @cons x s e es x' xend hstep hrest ih =>
      have he : e=3 := hall e (by simp)
      subst e
      have hstep' : x + 14*P = 8*x' + 2*(c+3+s) := by
        simpa using hstep
      have hstepI : (x : Int) + 14*(P : Int) =
          8*(x' : Int) + 2*((c : Int)+3+(s : Int)) := by
        exact_mod_cast hstep'
      have hscale :
          8*restartEnergy P c (s+3) x' =
            restartEnergy P c s x := by
        unfold restartEnergy
        simp [Nat.cast_add]
        omega
      have hallTail : ∀ f, f ∈ es → f=3 := by
        intro f hf
        exact hall f (by simp [hf])
      have htail := ih hallTail
      have hresult :
          restartEnergy P c s x =
            (8 : Int)^(es.length+1) *
              restartEnergy P c (s+3+totalCost es) xend := by
        calc
          restartEnergy P c s x =
              8*restartEnergy P c (s+3) x' := hscale
          _ = 8*((8 : Int)^es.length *
                restartEnergy P c (s+3+totalCost es) xend) := by
                rw [htail]
          _ = (8 : Int)^(es.length+1) *
                restartEnergy P c (s+3+totalCost es) xend := by
                rw [pow_succ]
                ac_rfl
      simpa [totalCost, Nat.add_assoc] using hresult

/-- In a restart suffix with edge costs 1..3, the first shallow edge is
    preceded only by depth-two edges (cost 3). -/
theorem exists_first_shallow
    (es : List Nat)
    (hpos : ∀ e, e ∈ es → 1 ≤ e)
    (hlow : ∀ e, e ∈ es → e ≤ 3)
    (hshallow : ∃ e, e ∈ es ∧ e ≤ 2) :
    ∃ pre e post, es=pre++[e]++post ∧ 1 ≤ e ∧ e ≤ 2 ∧
      (∀ u, u ∈ pre → u=3) := by
  induction es with
  | nil =>
      rcases hshallow with ⟨e, he, _⟩
      simp at he
  | cons a es ih =>
      by_cases ha : a ≤ 2
      · refine ⟨[], a, es, by simp, hpos a (by simp), ha, ?_⟩
        intro u hu
        simp at hu
      · have ha3 : a=3 := by
          have h := hlow a (by simp)
          omega
        have hshallowTail : ∃ e, e ∈ es ∧ e ≤ 2 := by
          rcases hshallow with ⟨e, he, he2⟩
          simp at he
          rcases he with he | he
          · subst e
            omega
          · exact ⟨e, he, he2⟩
        have hposTail : ∀ e, e ∈ es → 1 ≤ e := by
          intro e he
          exact hpos e (by simp [he])
        have hlowTail : ∀ e, e ∈ es → e ≤ 3 := by
          intro e he
          exact hlow e (by simp [he])
        obtain ⟨pre,e,post,hEq,hepos,he2,hpre⟩ :=
          ih hposTail hlowTail hshallowTail
        refine ⟨a::pre,e,post,?_,hepos,he2,?_⟩
        · simp [hEq, List.append_assoc]
        · intro u hu
          simp at hu
          rcases hu with rfl | hu
          · exact ha3
          · exact hpre u hu

/-- Every wall-reaching source restart path has a first shallow edge; its
    prefix is a string of exact depth-two edges. -/
theorem restartPath_first_shallow
    (n b d m : Nat) (path : RestartPath n b d m)
    (hbound : 2^path.L ≤ 7*weightS 0 path.es) :
    ∃ pre e post, path.es=pre++[e]++post ∧ 1 ≤ e ∧ e ≤ 2 ∧
      (∀ u, u ∈ pre → u=3) := by
  exact exists_first_shallow path.es path.hPos path.hLow
    (restart_path_has_shallow path hbound)

end BB6.Agent9RestartWallLowTrace
