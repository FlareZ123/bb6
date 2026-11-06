import PhysicalTraceAudit

namespace BB6Coverage

def finiteRayTapeEq (c d : FinRayCfg) : Bool :=
  c.ones.all (fun x => d.ones.contains x) &&
    d.ones.all (fun x => c.ones.contains x)

def finiteRayCfgEq (c d : FinRayCfg) : Bool :=
  decide (c.state = d.state ∧ c.head = d.head) && finiteRayTapeEq c d

theorem finiteRayTapeEq_sound (c d : FinRayCfg)
    (h : finiteRayTapeEq c d = true) :
    ∀ x, finiteTape c x = finiteTape d x := by
  have hpair :
      c.ones.all (fun x => d.ones.contains x) = true ∧
      d.ones.all (fun x => c.ones.contains x) = true := by
    simpa only [finiteRayTapeEq, Bool.and_eq_true] using h
  intro x
  apply Bool.eq_iff_iff.mpr
  change c.ones.contains x = true ↔ d.ones.contains x = true
  constructor
  · intro hx
    have hxmem : x ∈ c.ones := List.contains_iff_mem.mp hx
    exact (List.all_eq_true.mp hpair.1) x hxmem
  · intro hx
    have hxmem : x ∈ d.ones := List.contains_iff_mem.mp hx
    exact (List.all_eq_true.mp hpair.2) x hxmem

theorem finiteRayCfgEq_embed (c d : FinRayCfg)
    (h : finiteRayCfgEq c d = true) :
    embedFinRay c = embedFinRay d := by
  have hbool : decide (c.state = d.state ∧ c.head = d.head) = true ∧
      finiteRayTapeEq c d = true := by
    simpa only [finiteRayCfgEq, Bool.and_eq_true] using h
  have hpair : c.state = d.state ∧ c.head = d.head := by
    simpa only [decide_eq_true_eq] using hbool.1
  have htape : ∀ x, finiteTape c x = finiteTape d x :=
    finiteRayTapeEq_sound c d hbool.2
  cases c with
  | mk cs ch co =>
    cases d with
    | mk ds dh do_ =>
      cases hpair.1
      cases hpair.2
      apply congrArg (fun tape : Int → Bool =>
        ({ state := cs, head := ch, tape := tape } : Config))
      funext x
      exact htape x

theorem lasso_run_add (m : Machine) (c : Config) (n k : Nat) :
    run m (n+k) c = (run m n c).bind (run m k) := by
  induction k with
  | zero => simp [run]
  | succ k ih =>
    rw [Nat.add_succ, run, ih]
    cases h : run m n c <;> simp [h, run]

theorem lasso_run_periodic (m : Machine) (c : Config) (k : Nat)
    (hcycle : run m k c = some c) :
    ∀ n, run m (k+n) c = run m n c := by
  intro n
  rw [lasso_run_add, hcycle]
  rfl

theorem lasso_run_prefix_exists (m : Machine) (c : Config) (k : Nat)
    (h : (run m k c).isSome = true) :
    ∀ n, n ≤ k → (run m n c).isSome = true := by
  intro n hn
  induction k generalizing n with
  | zero =>
    have : n = 0 := by omega
    subst n
    simpa [run] using h
  | succ k ih =>
    by_cases heq : n = k+1
    · subst n
      exact h
    · have hn' : n ≤ k := by omega
      have hprev : (run m k c).isSome = true := by
        cases hr : run m k c with
        | none => simp [run, hr] at h
        | some d => rfl
      exact ih hprev n hn'

theorem lasso_run_cycle_never (m : Machine) (c : Config) (k : Nat)
    (hk : 0 < k) (hcycle : run m k c = some c) :
    ∀ n, (run m n c).isSome = true := by
  intro n
  refine Nat.strongRecOn n ?_
  intro n ih
  by_cases hlt : n < k
  · exact lasso_run_prefix_exists m c k (by simp [hcycle]) n
      (Nat.le_of_lt hlt)
  · have hle : k ≤ n := Nat.le_of_not_gt hlt
    have hsub : n-k < n := by omega
    have hper := lasso_run_periodic m c k hcycle (n-k)
    have heq : k + (n-k) = n := Nat.add_sub_of_le hle
    rw [← heq, hper]
    exact ih (n-k) hsub

theorem lasso_run_repeat_never (m : Machine) (k n : Nat) (c : Config)
    (hk : run m k blank = some c)
    (hn : run m n blank = some c)
    (hkn : k < n) : NeverHalts m := by
  have hlen : 0 < n-k := by omega
  have hsum : k + (n-k) = n := Nat.add_sub_of_le (Nat.le_of_lt hkn)
  have hadd := lasso_run_add m blank k (n-k)
  rw [hsum] at hadd
  have hadd' : run m n blank = run m (n-k) c := by
    simpa [hk] using hadd
  have hcycle : run m (n-k) c = some c := by
    calc
      run m (n-k) c = run m n blank := hadd'.symm
      _ = some c := hn
  intro t
  by_cases ht : t < k
  · exact lasso_run_prefix_exists m blank k (by simp [hk]) t
      (Nat.le_of_lt ht)
  · have hle : k ≤ t := Nat.le_of_not_gt ht
    have hsum' : k + (t-k) = t := Nat.add_sub_of_le hle
    have hprefix : run m t blank = run m (t-k) c := by
      calc
        run m t blank = run m (k+(t-k)) blank := by rw [hsum']
        _ = (run m k blank).bind (run m (t-k)) :=
          lasso_run_add m blank k (t-k)
        _ = run m (t-k) c := by simp [hk]
    rw [hprefix]
    exact lasso_run_cycle_never m c (n-k) hlen hcycle (t-k)

def finiteLassoCheck (p : PartialMachine) (n : Nat) : Bool :=
  match finitePartialRun p n finiteBlank with
  | none => false
  | some c =>
      (List.range n).any (fun k =>
        match finitePartialRun p k finiteBlank with
        | none => false
        | some d => finiteRayCfgEq c d)

def finiteLassoOracle (p : PartialMachine) (maxSteps : Nat) : Bool :=
  (List.range (maxSteps+1)).any (finiteLassoCheck p)

theorem finiteLassoCheck_sound (p : PartialMachine) (n bound : Nat)
    (h : finiteLassoCheck p n = true) :
    Cover (DecidedBelow bound) p := by
  cases hrun : finitePartialRun p n finiteBlank with
  | none => simp [finiteLassoCheck, hrun] at h
  | some c =>
    have hscan : (List.range n).any (fun k =>
        match finitePartialRun p k finiteBlank with
        | none => false
        | some d => finiteRayCfgEq c d) = true := by
      simpa [finiteLassoCheck, hrun] using h
    obtain ⟨k, hk, hsame⟩ := List.any_eq_true.mp hscan
    have hkn : k < n := List.mem_range.mp hk
    cases hprev : finitePartialRun p k finiteBlank with
    | none => simp [hprev] at hsame
    | some d =>
      have hcfgEq : finiteRayCfgEq c d = true := by
        simpa [hprev] using hsame
      have hcfg : embedFinRay c = embedFinRay d :=
        finiteRayCfgEq_embed c d hcfgEq
      apply Cover.leaf
      intro m hm
      left
      have hnrun := finitePartialRun_sound p m hm finiteBlank c n hrun
      have hkrun := finitePartialRun_sound p m hm finiteBlank d k hprev
      have hkrun' : run m k blank = some (embedFinRay c) := by
        rw [embedFinRay_blank] at hkrun
        rw [← hcfg] at hkrun
        exact hkrun
      rw [embedFinRay_blank] at hnrun
      exact lasso_run_repeat_never m k n (embedFinRay c) hkrun' hnrun hkn

theorem finiteLassoOracle_sound (p : PartialMachine) (maxSteps bound : Nat)
    (h : finiteLassoOracle p maxSteps = true) :
    Cover (DecidedBelow bound) p := by
  obtain ⟨n, _, hn⟩ := List.any_eq_true.mp h
  exact finiteLassoCheck_sound p n bound hn

def readOneLassoTable : PartialMachine := fun slot =>
  if slot = (⟨0, by decide⟩, false) then
    some (some ⟨true, true, ⟨1, by decide⟩⟩)
  else if slot = (⟨1, by decide⟩, false) then
    some (some ⟨false, false, ⟨0, by decide⟩⟩)
  else if slot = (⟨0, by decide⟩, true) then
    some (some ⟨false, true, ⟨1, by decide⟩⟩)
  else none

theorem readOneLasso_four_moves :
    finitePartialRun readOneLassoTable 4 finiteBlank = some finiteBlank := by
  rfl

theorem readOneLasso_check : finiteLassoCheck readOneLassoTable 4 = true := by
  decide

theorem readOneLasso_old_oracle_misses :
    finiteDecisionOracle readOneLassoTable 6 6 = false := by
  decide

theorem readOneLasso_cover :
    Cover (DecidedBelow 6) readOneLassoTable :=
  finiteLassoCheck_sound readOneLassoTable 4 6 readOneLasso_check

theorem readOneLasso_mass :
    cylinderMass readOneLassoTable = 25^9 := by
  decide

theorem readOneLasso_mass_numeric :
    cylinderMass readOneLassoTable = 3814697265625 := by
  rw [readOneLasso_mass]
  decide

theorem readOneLasso_works (m : Machine)
    (hm : compatible readOneLassoTable m) : DecidedBelow 6 m :=
  readOneLasso_cover.sound m hm

#print axioms finiteRayCfgEq_embed
#print axioms lasso_run_repeat_never
#print axioms finiteLassoCheck_sound
#print axioms finiteLassoOracle_sound
#print axioms readOneLasso_four_moves
#print axioms readOneLasso_check
#print axioms readOneLasso_old_oracle_misses
#print axioms readOneLasso_cover
#print axioms readOneLasso_mass
#print axioms readOneLasso_mass_numeric
#print axioms readOneLasso_works

end BB6Coverage
