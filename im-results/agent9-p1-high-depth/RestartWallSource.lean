import HighDepthRestartSource
import RestartWallTelescoping

set_option maxRecDepth 8192

namespace BB6.Agent9RestartWallSource

open BB6.Agent1Quarter BB6.Agent47P1
open BB6.Agent43HighDepthRestart
open BB6.Agent9RestartWallTelescoping

/-- Append one source transition to the end of a restart walk. The transition
    is stated at the cumulative relative cost after the existing word. -/
theorem restart_walk_snoc
    (P c x0 s : Nat) (es : List Nat) (x e x' : Nat)
    (h : RestartWalk P c x0 s es x)
    (hstep : x + 14*P = 2^e*x' + 2*(c+3+s+totalCost es)) :
    RestartWalk P c x0 s (es ++ [e]) x' := by
  induction h generalizing e x' with
  | nil x s =>
      have hstep' : x + 14*P = 2^e*x' + 2*(c+3+s) := by
        simpa [totalCost] using hstep
      exact RestartWalk.cons hstep' (RestartWalk.nil x' (s+e))
  | @cons x s e0 es xmid xend hfirst hrest ih =>
      have hstep' : xend + 14*P =
          2^e*x' + 2*(c+3+(s+e0)+totalCost es) := by
        simpa [totalCost, Nat.add_assoc] using hstep
      have htail := ih hstep'
      simpa [List.append_assoc] using RestartWalk.cons hfirst htail

theorem totalCost_append_singleton (es : List Nat) (e : Nat) :
    totalCost (es ++ [e]) = totalCost es + e := by
  induction es with
  | nil => simp [totalCost]
  | cons a es ih => simp [totalCost, ih, Nat.add_assoc]

/-- A restart path is an actual suffix of an OddCone history beginning
    immediately after a depth-at-least-three edge. The walk records every
    subsequent original inverse transition, not merely its scalar projection. -/
structure RestartPath (n b d m : Nat) : Type where
  m0 : Nat
  c : Nat
  x0 : Nat
  xhalf : Nat
  L : Nat
  es : List Nat
  hBase : c = m0+n
  hCost : m = m0+L
  hTotal : totalCost es = L
  hPos : ∀ e, e ∈ es → 1 ≤ e
  hLow : ∀ e, e ∈ es → e ≤ 3
  hEven : x0 = 2*xhalf
  hHalf : xhalf < 2^n
  walk : RestartWalk (2^n) c x0 0 es (d-1)
  /-- Exact source OddCone suffix from the child of the last deep edge. -/
  b0 : Nat
  d0 : Nat
  suffix : OddCone b0 d0 b d L
  /-- The RestartWalk begins at the right counter of the suffix root. -/
  hSuffixStart : x0=d0-1
  /-- Absolute source mass at the restart child (relative suffix cost 0). -/
  hStartMass : b0+d0+2*m0+2*n+13=14*2^n
  /-- Source inverse depths and scalar restart costs differ by one. -/
  hDepths : (oddConeDepths suffix).map Nat.succ = es

/-- Immediately after any authentic depth>=3 edge, the exact source defect
    supplies the even restart half-defect required by the telescoping lemma. -/
theorem restart_path_after_deep
    (n bp dp mp t k cInv : Nat)
    (hn : 14 ≤ n)
    (hpre : OddCone (14*2^n-2*n-16) 3 bp dp mp)
    (hb : 8 ≤ bp) (hb4 : bp%4=0) (hd : dp%2=1)
    (hi : inverseAt bp dp t = some (k,cInv))
    (hk : 2 ≤ k) (hc : cInv%2=1)
    (hdeep : 3 ≤ t) :
    RestartPath n (2*k-4) (cInv+4) (mp+t+1) := by
  have hmass0 := odd_cone_mass _ _ bp dp mp hpre
  have hroot : (14*2^n-2*n-16)+3+2*n+13 = 14*2^n := by omega
  have hmass : bp+dp+2*mp+2*n+13 = 14*2^n := by omega
  have hsource := (inverseAt_iff_power_mass bp dp t k cInv (by omega) hb4 hd).mp hi
  have hpower := hsource.1
  have hinvMass : 2*k+cInv+2*t+2=bp+dp := by
    simpa [hc] using hsource.2
  have hFdeep := defect_deep_positive n bp dp mp t k cInv
    hn hmass hb4 hpower hinvMass hk hdeep
  have hpost : OddCone (14*2^n-2*n-16) 3
      (2*k-4) (cInv+4) (mp+t+1) :=
    OddCone.parent bp dp mp t k cInv hpre hb hb4 hd hi hk hc
  have hmassPost0 := odd_cone_mass _ _ (2*k-4) (cInv+4) (mp+t+1) hpost
  have hmassPost :
      (2*k-4)+(cInv+4)+2*(mp+t+1)+2*n+13 = 14*2^n := by omega
  obtain ⟨xhalf, hxhalf, hxsmall⟩ :=
    restart_half_defect_lt_of_int (2^n) n (2*k-4) (cInv+4) (mp+t+1)
      rfl hmassPost hFdeep (by omega)
  have hEven : cInv+3 = 2*xhalf := by omega
  refine {
    m0 := mp+t+1
    c := mp+t+1+n
    x0 := cInv+3
    xhalf := xhalf
    L := 0
    es := []
    hBase := rfl
    hCost := by simp
    hTotal := rfl
    hPos := by intro e he; simp at he
    hLow := by intro e he; simp at he
    hEven := hEven
    hHalf := hxsmall
    walk := ?_
    b0 := 2*k-4
    d0 := cInv+4
    suffix := OddCone.root
    hSuffixStart := by omega
    hStartMass := hmassPost
    hDepths := by simp [oddConeDepths]
  }
  have hnil : RestartWalk (2^n) (mp+t+1+n) (cInv+3) 0 [] (cInv+3) :=
    RestartWalk.nil (cInv+3) 0
  have hEq : cInv+3 = (cInv+4)-1 := by omega
  simpa [hEq] using hnil

/-- Append one unchanged-source inverseAt edge to a restart path. -/
theorem restart_path_extend
    (n bp dp mp t k cInv : Nat)
    (hmass : bp+dp+2*mp+2*n+13 = 14*2^n)
    (hb : 8 ≤ bp) (hb4 : bp%4=0) (hd : dp%2=1)
    (hi : inverseAt bp dp t = some (k,cInv))
    (hk : 2 ≤ k) (hc : cInv%2=1) (ht : t ≤ 2)
    (path : RestartPath n bp dp mp) :
    RestartPath n (2*k-4) (cInv+4) (mp+t+1) := by
  have hsource := (inverseAt_iff_power_mass bp dp t k cInv (by omega) hb4 hd).mp hi
  have hpower := hsource.1
  have hInv2 : 2*dp+bp+6 = 2^(t+1)*(cInv+3) := by
    calc
      2*dp+bp+6 = 2*(dp+bp/2+3) := by omega
      _ = 2*(2^t*(cInv+3)) := by rw [hpower]
      _ = 2^(t+1)*(cInv+3) := by rw [Nat.pow_succ]; ac_rfl
  have hStepSource := source_edge_recurrence
    (2^n) n bp dp mp t cInv hmass hInv2 (by omega)
  have hStepRestart :
      dp-1+14*2^n =
        2^(t+1)*(cInv+3)+2*(path.c+3+totalCost path.es) := by
    rw [hStepSource]
    have hBase := path.hBase
    have hCost := path.hCost
    have hTotal := path.hTotal
    omega
  have hWalk := restart_walk_snoc
    (P:=2^n) (c:=path.c) (x0:=path.x0) (s:=0)
    (es:=path.es) (x:=dp-1) (e:=t+1) (x':=cInv+3)
    path.walk hStepRestart
  have hEq : cInv+3 = (cInv+4)-1 := by omega
  refine {
    m0 := path.m0
    c := path.c
    x0 := path.x0
    xhalf := path.xhalf
    L := path.L+(t+1)
    es := path.es++[t+1]
    b0 := path.b0
    d0 := path.d0
    suffix := OddCone.parent bp dp path.L t k cInv path.suffix hb hb4 hd hi hk hc
    hSuffixStart := path.hSuffixStart
    hStartMass := path.hStartMass
    hDepths := by
      simp [oddConeDepths, List.map_append, path.hDepths]
    hBase := path.hBase
    hCost := ?_
    hTotal := ?_
    hPos := ?_
    hLow := ?_
    hEven := path.hEven
    hHalf := path.hHalf
    walk := ?_
  }
  · rw [path.hCost]
    omega
  · calc
      totalCost (path.es++[t+1]) = totalCost path.es+(t+1) :=
        totalCost_append_singleton path.es (t+1)
      _ = path.L+(t+1) := by rw [path.hTotal]
  · intro e he
    rcases List.mem_append.mp he with heOld | heLast
    · exact path.hPos e heOld
    · simp at heLast
      subst e
      omega
  · intro e he
    rcases List.mem_append.mp he with heOld | heLast
    · exact path.hLow e heOld
    · simp at heLast
      subst e
      omega
  · simpa [hEq] using hWalk

/-- A source history either has no depth>=3 edge, or carries the exact
    restart path after its most recent such edge. Every later t=0,1,2 edge
    is appended to that same source path; a later t>=3 edge resets it. -/
inductive RestartState (n : Nat) (xs : List Nat) (b d m : Nat) : Type where
  | noDeep (hNo : NoDeep xs) : RestartState n xs b d m
  | active (hDeep : HasDeep xs) (path : RestartPath n b d m) :
      RestartState n xs b d m

theorem restart_state_of_odd_cone
    (n b d m : Nat) (hn : 14 ≤ n)
    (h : OddCone (14*2^n-2*n-16) 3 b d m) :
    RestartState n (oddConeDepths h) b d m := by
  induction h with
  | root =>
      exact RestartState.noDeep (by
        intro t ht
        simp [oddConeDepths] at ht)
  | parent bp dp mp t k cInv hpre hb hb4 hd hi hk hc ih =>
      have hmass0 := odd_cone_mass _ _ bp dp mp hpre
      have hroot : (14*2^n-2*n-16)+3+2*n+13 = 14*2^n := by omega
      have hmass : bp+dp+2*mp+2*n+13 = 14*2^n := by omega
      cases ih with
      | noDeep hNo =>
          by_cases hdeep : 3 ≤ t
          · have path := restart_path_after_deep n bp dp mp t k cInv
              hn hpre hb hb4 hd hi hk hc hdeep
            exact RestartState.active
              (hasDeep_append_last (oddConeDepths hpre) t hdeep) path
          · exact RestartState.noDeep
              (noDeep_append_singleton hNo (by omega))
      | active hDeep path =>
          by_cases hdeep : 3 ≤ t
          · have path' := restart_path_after_deep n bp dp mp t k cInv
              hn hpre hb hb4 hd hi hk hc hdeep
            exact RestartState.active
              (hasDeep_append_last (oddConeDepths hpre) t hdeep) path'
          · have path' := restart_path_extend n bp dp mp t k cInv
              hmass hb hb4 hd hi hk hc (by omega) path
            exact RestartState.active
              (hasDeep_append_singleton (oddConeDepths hpre) t hDeep) path'

/-- For every genuine critical OddCone wall history containing at least one
    depth>=3 inverse edge, the suffix after its last such edge has an exact
    RestartWalk and satisfies 2^L <= 7*S. This is a necessary source condition,
    not a P1 blank-root decision. -/
theorem source_wall_restart_path
    (n b d m : Nat) (hn : 14 ≤ n)
    (h : OddCone (14*2^n-2*n-16) 3 b d m)
    (hwall : b+4*m+4*n+20 = 12*2^n)
    (hdeep : HasDeep (oddConeDepths h)) :
    ∃ path : RestartPath n b d m,
      2^path.L ≤ 7*weightS 0 path.es := by
  have hstate := restart_state_of_odd_cone n b d m hn h
  cases hstate with
  | noDeep hNo =>
      exact False.elim (hasDeep_not_noDeep hdeep hNo)
  | active _ path =>
      have hmass0 := odd_cone_mass _ _ b d m h
      have hroot : (14*2^n-2*n-16)+3+2*n+13 = 14*2^n := by omega
      have hmass : b+d+2*m+2*n+13 = 14*2^n := by omega
      have hwallD := source_wall_endpoint (2^n) n b d m hmass hwall
      have hwallX : d-1 = 2*2^n+2*path.L+2*path.c+6 := by
        rw [hwallD]
        have hBase := path.hBase
        have hCost := path.hCost
        omega
      have htel := restart_walk_telescopes
        (2^n) path.c path.x0 0 (d-1) path.es path.walk
      have htel' :
          path.x0+14*2^n*weightS 0 path.es =
            2^path.L*(d-1)+
              2*((path.c+3)*weightS 0 path.es+weightT 0 path.es) := by
        simpa [path.hTotal] using htel
      have hInvWall :
          2*path.xhalf+14*2^n*(weightS 0 path.es) =
            2^path.L*(2*2^n+2*path.L+2*path.c+6)+
              2*((path.c+3)*weightS 0 path.es+weightT 0 path.es) := by
        calc
          2*path.xhalf+14*2^n*(weightS 0 path.es) =
              path.x0+14*2^n*(weightS 0 path.es) := by rw [path.hEven]
          _ = 2^path.L*(d-1)+
                2*((path.c+3)*weightS 0 path.es+weightT 0 path.es) := htel'
          _ = 2^path.L*(2*2^n+2*path.L+2*path.c+6)+
                2*((path.c+3)*weightS 0 path.es+weightT 0 path.es) := by
                rw [hwallX]
      have hid := restart_wall_identity_from_invariant
        (2^n) path.c path.xhalf path.L
        (weightS 0 path.es) (weightT 0 path.es) hInvWall
      have hbound := restart_wall_nonnegative_N
        (2^n) path.L (weightS 0 path.es) (weightT 0 path.es)
        path.c path.xhalf hid path.hHalf
      exact ⟨path, hbound⟩

#print axioms restart_walk_snoc
#print axioms restart_path_after_deep
#print axioms restart_path_extend
#print axioms restart_state_of_odd_cone
theorem weightS_all_three
    (s : Nat) (es : List Nat)
    (hall : ∀ e, e ∈ es → e=3) :
    7*weightS s es + 2^s = 2^(s+totalCost es) := by
  induction es generalizing s with
  | nil =>
      simp [weightS, totalCost]
  | cons e es ih =>
      have he : e=3 := hall e (by simp)
      have htail : ∀ u, u ∈ es → u=3 := by
        intro u hu
        exact hall u (by simp [hu])
      subst e
      simp only [weightS, totalCost]
      have ih' := ih (s+3) htail
      have hpow : 2^(s+3)=8*2^s := by
        calc
          2^(s+3) = 2^s*2^3 := Nat.pow_add 2 s 3
          _ = 2^s*8 := by norm_num
          _ = 8*2^s := by ac_rfl
      calc
        7*(2^s+weightS (s+3) es)+2^s =
            7*weightS (s+3) es+2^(s+3) := by rw [hpow]; omega
        _ = 2^((s+3)+totalCost es) := ih'
        _ = 2^(s+(3+totalCost es)) := by congr 1 <;> omega

/-- A nonnegative restart product forces at least one shallow edge in the
    post-last-deep suffix, because that suffix contains only costs 1, 2, 3. -/
theorem restart_path_has_shallow
    {n b d m : Nat} (path : RestartPath n b d m)
    (hbound : 2^path.L ≤ 7*weightS 0 path.es) :
    ∃ e, e ∈ path.es ∧ e ≤ 2 := by
  by_contra hnone
  have hall : ∀ e, e ∈ path.es → e=3 := by
    intro e he
    have hle := path.hLow e he
    have hgt : 2 < e := by
      by_contra hgt
      exact hnone ⟨e,he,by omega⟩
    omega
  have hEq := weightS_all_three 0 path.es hall
  have hEq' : 7*weightS 0 path.es+1 = 2^path.L := by
    simpa [path.hTotal] using hEq
  omega

/-- Locate the last shallow edge in a finite low-depth suffix. Everything
    after it has inverse cost 3 (depth exactly two). -/
theorem exists_last_shallow
    (es : List Nat)
    (hLow : ∀ e, e ∈ es → e≤3)
    (hShallow : ∃ e, e ∈ es ∧ e≤2) :
    ∃ pre e post, es=pre++[e]++post ∧ e≤2 ∧
      (∀ u, u ∈ post → u=3) := by
  induction es with
  | nil =>
      rcases hShallow with ⟨e,he,_⟩
      exact False.elim (by simpa using he)
  | cons a es ih =>
      by_cases htail : ∃ e, e ∈ es ∧ e≤2
      · have hLowTail : ∀ e, e ∈ es → e≤3 := by
          intro e he
          exact hLow e (by simp [he])
        obtain ⟨pre,e,post,hEq,he2,hpost⟩ := ih hLowTail htail
        refine ⟨a::pre,e,post,?_,he2,hpost⟩
        simp [hEq, List.append_assoc]
      · have hHead : a≤2 := by
          rcases hShallow with ⟨e,he,he2⟩
          simp at he
          rcases he with hHead | hTail
          · subst e
            exact he2
          · exact False.elim (htail ⟨e,hTail,he2⟩)
        refine ⟨[],a,es,by simp,hHead,?_⟩
        intro u hu
        have hLowU := hLow u (by simp [hu])
        have hNotLe : ¬ u≤2 := by
          intro hle
          exact htail ⟨u,hu,hle⟩
        omega

/-- Original-source form of the restart suffix conclusion: after the last
    depth>=3 edge, a wall-reaching history has a shallow edge, and after its
    last shallow edge all remaining inverse edges have depth exactly two. -/
theorem source_wall_restart_suffix_shape
    (n b d m : Nat) (hn : 14 ≤ n)
    (h : OddCone (14*2^n-2*n-16) 3 b d m)
    (hwall : b+4*m+4*n+20 = 12*2^n)
    (hdeep : HasDeep (oddConeDepths h)) :
    ∃ path : RestartPath n b d m,
      2^path.L ≤ 7*weightS 0 path.es ∧
      ∃ pre e post,
        path.es=pre++[e]++post ∧ 1≤e ∧ e≤2 ∧
          (∀ u, u ∈ post → u=3) := by
  obtain ⟨path,hbound⟩ := source_wall_restart_path n b d m hn h hwall hdeep
  obtain ⟨e,heMem,heLow⟩ := restart_path_has_shallow path hbound
  obtain ⟨pre,e,post,hEq,he2,hpost⟩ :=
    exists_last_shallow path.es path.hLow ⟨e,heMem,heLow⟩
  exact ⟨path,hbound,pre,e,post,hEq,path.hPos e heMem,he2,hpost⟩

#print axioms source_wall_restart_path
#print axioms source_wall_restart_suffix_shape

end BB6.Agent9RestartWallSource
