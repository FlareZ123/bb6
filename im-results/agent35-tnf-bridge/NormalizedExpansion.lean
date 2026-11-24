def swapFun (a b s : Fin 6) : Fin 6 :=
  if s = a then b else if s = b then a else s

theorem swapFun_involutive (a b s : Fin 6) :
    swapFun a b (swapFun a b s) = s := by
  by_cases hab : a = b
  · subst b
    simp [swapFun]
  · by_cases hsa : s = a
    · subst s
      simp [swapFun, hab]
    · by_cases hsb : s = b
      · subst s
        simp [swapFun, hab]
      · simp [swapFun, hsa, hsb, hab]

def swapStatePerm (a b : Fin 6) : StatePerm where
  forward := swapFun a b
  backward := swapFun a b
  leftInverse := by
    intro s
    exact swapFun_involutive a b s
  rightInverse := by
    intro s
    exact swapFun_involutive a b s

theorem swapStatePerm_fix_below (m : Nat) (a b s : Fin 6)
    (ha : m ≤ a.val) (hb : m ≤ b.val) (hs : s.val < m) :
    (swapStatePerm a b).forward s = s ∧
    (swapStatePerm a b).backward s = s := by
  have hsa : s ≠ a := by
    intro h
    have hv := congrArg Fin.val h
    omega
  have hsb : s ≠ b := by
    intro h
    have hv := congrArg Fin.val h
    omega
  constructor <;> simp [swapStatePerm, hsa, hsb]

/-- State renaming that fixes the blank start preserves all-time nonhalting. -/
theorem renameNeverHalts_iff (e : StatePerm) (m : Machine)
    (hroot : e.forward (0 : Fin 6) = 0) :
    NeverHalts (renameTable e m) ↔ NeverHalts m := by
  constructor
  · intro h n
    have hrun : run (renameTable e m) n blank =
        (run m n blank).map (renameConfig e) := by
      simpa [renameConfig, blank, hroot] using rename_run e m blank n
    have hn := h n
    rw [hrun] at hn
    cases hr : run m n blank with
    | none => simp [hr] at hn
    | some d => simp [hr]
  · intro h n
    have hrun : run (renameTable e m) n blank =
        (run m n blank).map (renameConfig e) := by
      simpa [renameConfig, blank, hroot] using rename_run e m blank n
    have hn := h n
    rw [hrun]
    cases hr : run m n blank with
    | none => simp [hr] at hn
    | some d => simp [hr]

theorem renameHaltsAfter_iff (e : StatePerm) (m : Machine)
    (hroot : e.forward (0 : Fin 6) = 0) (n : Nat) :
    HaltsAfter (renameTable e m) n ↔ HaltsAfter m n := by
  have hblank : renameConfig e blank = blank := by
    simp [renameConfig, blank, hroot]
  have hrun : ∀ k, run (renameTable e m) k blank =
      (run m k blank).map (renameConfig e) := by
    intro k
    simpa [hblank] using (rename_run e m blank k)
  constructor
  · intro h
    constructor
    · have hn := h.1
      rw [hrun n] at hn
      cases hr : run m n blank with
      | none => simp [hr] at hn
      | some c => simp [hr]
    · have hn := h.2
      rw [hrun (n + 1)] at hn
      cases hr : run m (n + 1) blank with
      | none => simp [hr]
      | some c => simp [hr] at hn
  · intro h
    constructor
    · have hn := h.1
      rw [hrun n]
      cases hr : run m n blank with
      | none => simp [hr] at hn
      | some c => simp [hr]
    · have hn := h.2
      rw [hrun (n + 1)]
      cases hr : run m (n + 1) blank with
      | none => simp [hr]
      | some c => simp [hr] at hn

theorem renameDecidedBelow_iff (B : Nat) (e : StatePerm) (m : Machine)
    (hroot : e.forward (0 : Fin 6) = 0) :
    DecidedBelow B (renameTable e m) ↔ DecidedBelow B m := by
  unfold DecidedBelow
  constructor
  · intro h
    rcases h with hnever | ⟨n, hbound, hh⟩
    · exact Or.inl ((renameNeverHalts_iff e m hroot).mp hnever)
    · exact Or.inr ⟨n, hbound, (renameHaltsAfter_iff e m hroot n).mp hh⟩
  · intro h
    rcases h with hnever | ⟨n, hbound, hh⟩
    · exact Or.inl ((renameNeverHalts_iff e m hroot).mpr hnever)
    · exact Or.inr ⟨n, hbound, (renameHaltsAfter_iff e m hroot n).mpr hh⟩

/-- The explicit invariant encoded by TNF's least-unused-state rule:
    all source slots at labels >= m are unassigned, and every assigned
    ordinary transition targets a label < m. -/
structure TNFWellFormed (p : PartialMachine) (m : Nat) : Prop where
  rootUsed : 1 ≤ m
  stateBound : m ≤ 6
  unusedSource : ∀ s b, m ≤ s.val → p (s, b) = none
  targetUsed : ∀ s b mv, p (s, b) = some (some mv) → mv.next.val < m

/-- Soundness of one TNF-normalized expansion.

    At an unassigned slot whose source state is already used, it suffices
    to provide:
    * a certified halt leaf when that slot is assigned halt; and
    * proof-carrying covers only for successor states 0,...,m (the used
      states and the least unused state).

    Every raw successor state > m is transported to m by a transposition
    fixing all used states, hence fixing the blank start and preserving
    exact halting scores. The resulting proof is a genuine 25-way Cover,
    not an assumption that the smaller TNF child list is itself exhaustive. -/
theorem tnf_expansion_cover
    (B m : Nat) (p : PartialMachine) (h : Slot)
    (wf : TNFWellFormed p m)
    (hsource : h.1.val < m)
    (hhole : p h = none)
    (haltLeaf : ∀ machine, compatible (refine p h none) machine →
      DecidedBelow B machine)
    (canonical : ∀ (w r : Bool) (q : Fin 6), q.val ≤ m →
      Cover (DecidedBelow B) (refine p h (some ⟨w, r, q⟩))) :
    Cover (DecidedBelow B) p := by
  refine Cover.branch p h hhole ?_
  intro t _ht
  cases t with
  | none =>
      exact Cover.leaf (refine p h none) haltLeaf
  | some mv =>
      by_cases hcanon : mv.next.val ≤ m
      · exact canonical mv.write mv.right mv.next hcanon
      · have hmq : m < mv.next.val := by omega
        have hm6 : m < 6 := Nat.lt_trans hmq mv.next.isLt
        let a : Fin 6 := ⟨m, hm6⟩
        let e : StatePerm := swapStatePerm a mv.next
        have ha : m ≤ a.val := by simp [a]
        have hb : m ≤ mv.next.val := by omega
        have hneq : a ≠ mv.next := by
          intro heq
          have hv := congrArg Fin.val heq
          simp [a] at hv
          omega
        have hroot : e.forward (0 : Fin 6) = 0 := by
          have hzero : (0 : Fin 6).val < m := by
            have := wf.rootUsed
            omega
          exact (swapStatePerm_fix_below m a mv.next 0 ha hb hzero).1
        have hsourceFixed : e.backward h.1 = h.1 :=
          (swapStatePerm_fix_below m a mv.next h.1 ha hb hsource).2
        have htarget : e.forward mv.next = a := by
          simp [e, swapStatePerm, hneq, hneq.symm]
        have hcanonical : Cover (DecidedBelow B)
            (refine p h (some ⟨mv.write, mv.right, a⟩)) :=
          canonical mv.write mv.right a (by simp [a])
        refine Cover.leaf (refine p h (some mv)) ?_
        intro machine hcomp
        let machine' := renameTable e machine
        have hcomp' : compatible
            (refine p h (some ⟨mv.write, mv.right, a⟩)) machine' := by
          intro slot tr hs
          by_cases hslot : slot = h
          · subst slot
            have hs' : some (some ⟨mv.write, mv.right, a⟩) = some tr := by
              simpa [refine] using hs
            have htr : tr = some ⟨mv.write, mv.right, a⟩ :=
              (Option.some.inj hs').symm
            subst tr
            have hraw : machine h = some mv :=
              hcomp h (some mv) (by simp [refine])
            simp [machine', renameTable, hsourceFixed, hraw, renameMove, htarget]
          · have hp : p slot = some tr := by
              simpa [refine, hslot] using hs
            have hslotUsed : slot.1.val < m := by
              by_cases hge : m ≤ slot.1.val
              · have hnone := wf.unusedSource slot.1 slot.2 hge
                rw [hp] at hnone
                contradiction
              · omega
            have hback : e.backward slot.1 = slot.1 :=
              (swapStatePerm_fix_below m a mv.next slot.1 ha hb hslotUsed).2
            have hraw : machine slot = tr :=
              hcomp slot tr (by simp [refine, hslot, hp])
            cases tr with
            | none =>
                simp [machine', renameTable, hback, hraw]
            | some mv2 =>
                have htargetUsed : mv2.next.val < m :=
                  wf.targetUsed slot.1 slot.2 mv2 hp
                have hforward : e.forward mv2.next = mv2.next :=
                  (swapStatePerm_fix_below m a mv.next mv2.next ha hb htargetUsed).1
                simp [machine', renameTable, hback, hraw, renameMove, hforward]
        have hgood : DecidedBelow B machine' := hcanonical.sound machine' hcomp'
        change DecidedBelow B (renameTable e machine) at hgood
        exact (renameDecidedBelow_iff B e machine hroot).mp hgood

#print axioms tnf_expansion_cover

end BB6Coverage
