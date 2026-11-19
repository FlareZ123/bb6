import RestartWallSource
import Mod7SlackLeaf

set_option maxRecDepth 8192

namespace BB6.Agent9RestartWallLowTrace

open BB6.Agent9RestartWallSource
open BB6.Agent9RestartWallTelescoping
open BB6.Agent9Mod7Slack
open BB6.Agent43HighDepthRestart
open BB6.Agent1Quarter BB6.Agent47P1

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


/-- The absolute source mass propagates through a suffix rooted at
    an arbitrary restart child.  The suffix cost is relative, while m0
    records the absolute cost already spent before that child. -/
theorem oddCone_mass_from_start
    (n m0 b0 d0 b d L : Nat)
    (h : OddCone b0 d0 b d L)
    (hStartMass : b0+d0+2*m0+2*n+13=14*2^n) :
    b+d+2*(m0+L)+2*n+13=14*2^n := by
  induction h generalizing m0 hStartMass with
  | root =>
      simpa using hStartMass
  | @parent bp dp mp t k c hpre hb hb4 hd hi hk hc ih =>
      have hpreMass := ih m0 hStartMass
      have hsource :=
        (inverseAt_iff_power_mass bp dp t k c (by omega) hb4 hd).mp hi
      have hInvMass : 2*k+c+2*t+2=bp+dp := by omega
      omega

/-- The OddCone index m is exactly the sum of its original inverse costs
    (depth+1). -/
theorem oddCone_depths_cost
    {b0 d0 b d m : Nat} (h : OddCone b0 d0 b d m) :
    totalCost ((oddConeDepths h).map Nat.succ) = m := by
  induction h with
  | root =>
      simp [oddConeDepths, totalCost]
  | @parent bp dp mp t k c hpre hb hb4 hd hi hk hc ih =>
      simp [oddConeDepths, totalCost, ih, Nat.add_assoc]

/-- A restart walk with fixed start state and edge-cost word has a
    unique endpoint. -/
theorem restartWalk_endpoint_unique
    (P c x s : Nat) (es : List Nat) (x1 x2 : Nat)
    (h1 : RestartWalk P c x s es x1)
    (h2 : RestartWalk P c x s es x2) :
    x1=x2 := by
  induction h1 generalizing x2 with
  | nil x s =>
      cases h2
      rfl
  | @cons x s e es xmid xend hstep hrest ih =>
      cases h2 with
      | @cons _ _ _ _ xmid' _ hstep' hrest' =>
          have hmul : 2^e*xmid = 2^e*xmid' := by
            apply Nat.add_right_cancel
            exact hstep.symm.trans hstep'
          have hxmid : xmid=xmid' :=
            Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide : 0 < (2:Nat))) hmul
          subst xmid'
          exact ih hrest'

/-- Split a RestartWalk after a chosen prefix word. -/
theorem restartWalk_split
    (P c x s xend : Nat) (pre post : List Nat)
    (h : RestartWalk P c x s (pre++post) xend) :
    ∃ xmid,
      RestartWalk P c x s pre xmid ∧
      RestartWalk P c xmid (s+totalCost pre) post xend := by
  induction pre generalizing x s xend with
  | nil =>
      refine ⟨x, RestartWalk.nil x s, ?_⟩
      simpa using h
  | cons e pre ih =>
      cases h with
      | @cons x s e' es xmid xend hstep hrest =>
          have htail : RestartWalk P c xmid (s+e) (pre++post) xend := by
            simpa using hrest
          obtain ⟨xmid',hpre,htail'⟩ := ih htail
          refine ⟨xmid', RestartWalk.cons hstep hpre, ?_⟩
          simpa [totalCost, Nat.add_assoc] using htail'

/-- Reconstruct the restart walk directly from a source OddCone suffix,
    retaining its absolute mass origin. -/
theorem oddCone_to_restartWalk
    (n m0 b0 d0 b d L : Nat)
    (h : OddCone b0 d0 b d L)
    (hStartMass : b0+d0+2*m0+2*n+13=14*2^n) :
    RestartWalk (2^n) (m0+n) (d0-1) 0
      ((oddConeDepths h).map Nat.succ) (d-1) := by
  induction h generalizing m0 hStartMass with
  | root =>
      simpa [oddConeDepths] using (RestartWalk.nil (d0-1) 0)
  | @parent bp dp mp t k c hpre hb hb4 hd hi hk hc ih =>
      have hpreMass := oddCone_mass_from_start
        n m0 b0 d0 bp dp mp hpre hStartMass
      have hsource :=
        (inverseAt_iff_power_mass bp dp t k c (by omega) hb4 hd).mp hi
      have hpow : 2^(t+1)=2^t*2 := by rw [Nat.pow_succ]
      have hInv2 : 2*dp+bp+6=2^(t+1)*(c+3) := by
        calc
          2*dp+bp+6 = 2*(dp+bp/2+3) := by omega
          _ = 2*(2^t*(c+3)) := by rw [hsource.1]
          _ = (2^t*2)*(c+3) := by ac_rfl
          _ = 2^(t+1)*(c+3) := by rw [hpow]
      have hStepSource := source_edge_recurrence
        (2^n) n bp dp (m0+mp) t c hpreMass hInv2 (by omega)
      have hpreCost := oddCone_depths_cost hpre
      have hstep :
          dp-1+14*2^n =
            2^(t+1)*(c+3)+
              2*((m0+n)+3+totalCost ((oddConeDepths hpre).map Nat.succ)) := by
        rw [hStepSource, hpreCost]
        omega
      have hwalkPre := ih m0 hStartMass
      have hwalk := restart_walk_snoc
        (2^n) (m0+n) (d0-1) 0
        ((oddConeDepths hpre).map Nat.succ) (dp-1) (t+1) (c+3)
        hwalkPre hstep
      simpa [oddConeDepths, List.map_append] using hwalk

/-- Split a source OddCone suffix at its first depth below two.  The
    output child is a valid OddCone parent state if the suffix continues,
    and is the endpoint otherwise; in either case the caller may supply its
    mod-four guard. -/
theorem oddCone_first_shallow_split
    {b0 d0 b d m : Nat}
    (h : OddCone b0 d0 b d m)
    (hLow : ∀ t, t ∈ oddConeDepths h → t ≤ 2)
    (hShallow : ∃ t, t ∈ oddConeDepths h ∧ t ≤ 1)
    (hbWall : b%4=0) :
    ∃ bp dp mp t k c,
      ∃ pre : OddCone b0 d0 bp dp mp,
      ∃ post : List Nat,
        (∀ u, u ∈ oddConeDepths pre → u=2) ∧
        oddConeDepths h = oddConeDepths pre ++ [t] ++ post ∧
        8 ≤ bp ∧ bp%4=0 ∧ dp%2=1 ∧
        t ≤ 1 ∧ inverseAt bp dp t = some (k,c) ∧
        2 ≤ k ∧ c%2=1 ∧ (2*k-4)%4=0 := by
  induction h generalizing hLow hShallow hbWall with
  | root =>
      simp [oddConeDepths] at hShallow
  | @parent bp dp mp t k c hpre hb hb4 hd hi hk hc ih =>
      have hLowPre : ∀ u, u ∈ oddConeDepths hpre → u ≤ 2 := by
        intro u hu
        exact hLow u (by simp [oddConeDepths, hu])
      by_cases hShallowPre : ∃ u, u ∈ oddConeDepths hpre ∧ u ≤ 1
      · obtain ⟨bp',dp',mp',t',k',c',pre,post,hpre2,hEq,hb',hb4',hd',ht',hi',hk',hc',hguard⟩ :=
          ih hLowPre hShallowPre hb4
        refine ⟨bp',dp',mp',t',k',c',pre,post++[t],hpre2,?_,hb',hb4',hd',ht',hi',hk',hc',hguard⟩
        calc
          oddConeDepths h = oddConeDepths hpre ++ [t] := by
            simp [oddConeDepths]
          _ = (oddConeDepths pre ++ [t'] ++ post) ++ [t] := by
            rw [hEq]
          _ = oddConeDepths pre ++ [t'] ++ (post ++ [t]) := by
            simp [List.append_assoc]
      · have hpre2 : ∀ u, u ∈ oddConeDepths hpre → u=2 := by
          intro u hu
          have hle := hLowPre u hu
          have hgt : 1 < u := by
            by_contra hnot
            exact hShallowPre ⟨u,hu,by omega⟩
          omega
        have ht : t ≤ 1 := by
          rcases hShallow with ⟨u,hu,hu1⟩
          have hu' : u ∈ oddConeDepths hpre ++ [t] := by
            simpa [oddConeDepths] using hu
          rcases List.mem_append.mp hu' with hpreMem | hlast
          · exact False.elim (hShallowPre ⟨u,hpreMem,hu1⟩)
          · simp at hlast
            subst u
            exact hu1
        refine ⟨bp,dp,mp,t,k,c,hpre,[],hpre2,?_,hb,hb4,hd,ht,hi,hk,hc,?_⟩
        · simp [oddConeDepths]
        · simpa using hbWall

/-- The RestartPath source suffix has the same edge-cost list as its
    scalar walk, with each inverse depth increased by one.  This exposes the
    actual first-shallow source parent and its mod-four child guard. -/
theorem restartPath_first_shallow_source_split
    (n b d m : Nat) (path : RestartPath n b d m)
    (hbound : 2^path.L ≤ 7*weightS 0 path.es)
    (hwall : b+4*m+4*n+20=12*2^n) :
    ∃ bp dp mp t k c,
      ∃ pre : OddCone path.b0 path.d0 bp dp mp,
      ∃ post : List Nat,
        (∀ u, u ∈ oddConeDepths pre → u=2) ∧
        path.es = (oddConeDepths pre).map Nat.succ ++ [t+1] ++ post.map Nat.succ ∧
        bp+dp+2*(path.c+mp+6)+1=14*2^n ∧
        8 ≤ bp ∧ bp%4=0 ∧ dp%2=1 ∧
        t ≤ 1 ∧ inverseAt bp dp t = some (k,c) ∧
        2 ≤ k ∧ c%2=1 ∧ (2*k-4)%4=0 := by
  have hLow : ∀ u, u ∈ oddConeDepths path.suffix → u ≤ 2 := by
    intro u hu
    have hmem : u+1 ∈ path.es := by
      rw [← path.hDepths]
      exact List.mem_map.mpr ⟨u,hu,by omega⟩
    have hle := path.hLow (u+1) hmem
    omega
  have hShallow : ∃ u, u ∈ oddConeDepths path.suffix ∧ u ≤ 1 := by
    obtain ⟨e,he,he2⟩ := restart_path_has_shallow path hbound
    have he' : e ∈ (oddConeDepths path.suffix).map Nat.succ := by
      rw [path.hDepths]
      exact he
    rcases List.mem_map.mp he' with ⟨u,hu,heq⟩
    refine ⟨u,hu,?_⟩
    have heq' : u+1=e := by simpa using heq
    omega
  have hbWall : b%4=0 := by omega
  obtain ⟨bp,dp,mp,t,k,c,pre,post,hpre2,hEq,hb,hb4,hd,ht,hi,hk,hc,hguard⟩ :=
    oddCone_first_shallow_split path.suffix hLow hShallow hbWall
  have hMassAbs := oddCone_mass_from_start
    n path.m0 path.b0 path.d0 bp dp mp pre path.hStartMass
  have hMass : bp+dp+2*(path.c+mp+6)+1=14*2^n := by
    rw [path.hBase]
    omega
  refine ⟨bp,dp,mp,t,k,c,pre,post,hpre2,?_,hMass,hb,hb4,hd,ht,hi,hk,hc,hguard⟩
  rw [path.hDepths,hEq]
  simp [List.map_append]

/-- The scalar RestartWalk prefix before the first shallow edge ends
    at exactly the right counter carried by the source OddCone prefix. -/
theorem restartPath_first_shallow_state
    (n b d m : Nat) (path : RestartPath n b d m)
    (hbound : 2^path.L ≤ 7*weightS 0 path.es)
    (hwall : b+4*m+4*n+20=12*2^n) :
    ∃ bp dp mp t k c,
      ∃ pre : OddCone path.b0 path.d0 bp dp mp,
      ∃ post : List Nat,
        (∀ u, u ∈ oddConeDepths pre → u=2) ∧
        path.es = (oddConeDepths pre).map Nat.succ ++ [t+1] ++ post.map Nat.succ ∧
        bp+dp+2*(path.c+mp+6)+1=14*2^n ∧
        8 ≤ bp ∧ bp%4=0 ∧ dp%2=1 ∧
        t ≤ 1 ∧ inverseAt bp dp t = some (k,c) ∧
        2 ≤ k ∧ c%2=1 ∧ (2*k-4)%4=0 ∧
        ∃ xmid,
          xmid=dp-1 ∧
          RestartWalk (2^n) path.c path.x0 0
            ((oddConeDepths pre).map Nat.succ) xmid ∧
          RestartWalk (2^n) path.c xmid mp
            ([t+1]++post.map Nat.succ) (d-1) := by
  obtain ⟨bp,dp,mp,t,k,c,pre,post,hpre2,hEq,hMass,hb,hb4,hd,ht,hi,hk,hc,hguard⟩ :=
    restartPath_first_shallow_source_split n b d m path hbound hwall
  have hpreWalk0 := oddCone_to_restartWalk
    n path.m0 path.b0 path.d0 bp dp mp pre path.hStartMass
  have hpreWalk : RestartWalk (2^n) path.c path.x0 0
      ((oddConeDepths pre).map Nat.succ) (dp-1) := by
    simpa [path.hBase,path.hSuffixStart] using hpreWalk0
  have hpreCost : totalCost ((oddConeDepths pre).map Nat.succ) = mp :=
    oddCone_depths_cost pre
  have hfull : RestartWalk (2^n) path.c path.x0 0
      (((oddConeDepths pre).map Nat.succ) ++ ([t+1]++post.map Nat.succ))
      (d-1) := by
    simpa [hEq,List.append_assoc] using path.walk
  obtain ⟨xmid,hprefix,htail⟩ := restartWalk_split
    (2^n) path.c path.x0 0 (d-1)
    ((oddConeDepths pre).map Nat.succ) ([t+1]++post.map Nat.succ) hfull
  have hxmid : xmid=dp-1 :=
    restartWalk_endpoint_unique (2^n) path.c path.x0 0
      ((oddConeDepths pre).map Nat.succ) xmid (dp-1) hprefix hpreWalk
  have htail' : RestartWalk (2^n) path.c xmid mp
      ([t+1]++post.map Nat.succ) (d-1) := by
    simpa [hpreCost] using htail
  exact ⟨bp,dp,mp,t,k,c,pre,post,hpre2,hEq,hMass,hb,hb4,hd,ht,hi,hk,hc,hguard,
    xmid,hxmid,hprefix,htail'⟩

/-- In the Is=48, odd-offset branch, the first shallow edge has
    depth one.  With the correct inverse-mass constant (2t+2=4), its
    source equations force an even child parameter; no mod-four exclusion
    follows at this level. -/
theorem is48_odd_first_shallow_even_child
    (P b d T k c : Nat)
    (hP : P%4=0)
    (hcoord : b+14=6*d)
    (hmass : b+d+2*T+1=14*P)
    (hT : T%2=1)
    (hpow : 2*(c+3)=d+b/2+3)
    (hInvMass : 2*k+c+4=b+d) :
    d%4=1 ∧ (b/2)%4=0 ∧ k%2=0 := by
  have hd : d%4=1 := by omega
  have hq : b/2+7=3*d := by omega
  have hc : c+5=2*d := by omega
  have hk : 2*k+13=5*d := by omega
  have hqmod : (b/2)%4=0 := by omega
  have hkmod : k%2=0 := by omega
  exact ⟨hd,hqmod,hkmod⟩

/-- The two depth-zero branches surviving the first-shallow scalar filter
    have an even source inverse left parameter. -/
theorem is20_odd_first_shallow_even_child
    (P b d T k c : Nat)
    (hP : P%4=0)
    (hcoord : b+18=6*d)
    (hmass : b+d+2*T+1=14*P)
    (hT : T%2=1)
    (hpow : c+3=d+b/2+3)
    (hInvMass : 2*k+c+2=b+d) :
    d%4=1 ∧ (b/2)%4=2 ∧ k%2=0 := by
  have hd : d%4=1 := by omega
  have hq : b/2+9=3*d := by omega
  have hc : c+9=4*d := by omega
  have hk : 2*k+2=b/2 := by omega
  have hqmod : (b/2)%4=2 := by omega
  have hkmod : k%2=0 := by omega
  exact ⟨hd,hqmod,hkmod⟩

/-- The even-offset Is=48 branch likewise has a depth-zero edge with
    even source inverse left parameter. -/
theorem is48_even_first_shallow_even_child
    (P b d T k c : Nat)
    (hP : P%4=0)
    (hcoord : b+14=6*d)
    (hmass : b+d+2*T+1=14*P)
    (hT : T%2=0)
    (hpow : c+3=d+b/2+3)
    (hInvMass : 2*k+c+2=b+d) :
    d%4=3 ∧ (b/2)%4=2 ∧ k%2=0 := by
  have hd : d%4=3 := by omega
  have hq : b/2+7=3*d := by omega
  have hc : c+7=4*d := by omega
  have hk : 2*k+2=b/2 := by omega
  have hqmod : (b/2)%4=2 := by omega
  have hkmod : k%2=0 := by omega
  exact ⟨hd,hqmod,hkmod⟩


/-- A wall-reaching original OddCone history containing a deep edge induces
    an exact LowTrace from its last deep restart point to the shifted wall.
    This is the source-authentic bridge to the scalar mod-7 leaf. -/
theorem source_wall_restart_lowTrace
    (n b d m : Nat) (hn : 14 ≤ n)
    (h : OddCone (14*2^n-2*n-16) 3 b d m)
    (hwall : b+4*m+4*n+20=12*2^n)
    (hdeep : HasDeep (oddConeDepths h)) :
    ∃ path : RestartPath n b d m,
      LowTrace ((2^n : Nat) : Int)
        (restartEnergy (2^n) path.c 0 path.x0)
        (restartOffset path.c 0)
        (-112*restartOffset path.c path.L+384)
        (restartOffset path.c path.L) := by
  obtain ⟨path, hbound⟩ :=
    source_wall_restart_path n b d m hn h hwall hdeep
  have hmass0 := odd_cone_mass _ _ b d m h
  have hroot : (14*2^n-2*n-16)+3+2*n+13=14*2^n := by omega
  have hmass : b+d+2*m+2*n+13=14*2^n := by omega
  have htrace := restartPath_toLowTrace n b d m path
  have hwallEnergy := restartPath_wall_energy n b d m path hmass hwall
  exact ⟨path, by simpa [hwallEnergy] using htrace⟩

/-- The first shallow edge of the source-authentic restart suffix is
    preceded only by depth-two edges. -/
theorem source_wall_first_shallow
    (n b d m : Nat) (hn : 14 ≤ n)
    (h : OddCone (14*2^n-2*n-16) 3 b d m)
    (hwall : b+4*m+4*n+20=12*2^n)
    (hdeep : HasDeep (oddConeDepths h)) :
    ∃ path : RestartPath n b d m,
      ∃ pre e post, path.es=pre++[e]++post ∧ 1≤e ∧ e≤2 ∧
        (∀ u, u∈pre → u=3) := by
  obtain ⟨path, hbound⟩ :=
    source_wall_restart_path n b d m hn h hwall hdeep
  exact ⟨path, restartPath_first_shallow n b d m path hbound⟩

#print axioms restartStep_lowStep
#print axioms restartWalk_toLowTrace
#print axioms restartPath_toLowTrace
#print axioms restartPath_wall_energy
#print axioms restartPath_initial_mod7
#print axioms restartPath_initial_upper
#print axioms restartWalk_all_three_energy_scale
#print axioms source_wall_restart_lowTrace
#print axioms source_wall_first_shallow

end BB6.Agent9RestartWallLowTrace
