import BlockMacro

namespace BB6BlockFAR

/-- Reflect a primitive configuration in the head position. -/
def mirrorPrim (c : Prim) : Prim :=
  ⟨c.q, tail c.r, cons (c.r 0) c.l⟩

/-- Reverse every transition direction. -/
def mirrorTable (M : Table) : Table :=
  fun q b => (M q b).map fun mv => {mv with right := !mv.right}

@[simp] theorem cons_tail (r : Ray) : cons (r 0) (tail r) = r := by
  funext n
  cases n <;> simp [cons, tail]

@[simp] theorem tail_blank : tail blankRay = blankRay := by
  funext n
  rfl

theorem mirrorPrim_involutive (c : Prim) : mirrorPrim (mirrorPrim c) = c := by
  cases c with
  | mk q l r =>
    simp [mirrorPrim, cons, cons_tail]

theorem mirrorPrim_blank : mirrorPrim primBlank = primBlank := by
  simp [mirrorPrim, primBlank, blankRay, tail_blank]

theorem mirrorTable_involutive (M : Table) : mirrorTable (mirrorTable M) = M := by
  funext q b
  cases hm : M q b with
  | none => simp [mirrorTable, hm]
  | some mv => simp [mirrorTable, hm]

/-- One primitive step commutes with tape reflection and direction reversal. -/
theorem primStep_mirror (M : Table) (c : Prim) :
    primStep (mirrorTable M) (mirrorPrim c) =
      (primStep M c).map mirrorPrim := by
  cases hm : M c.q (c.r 0) with
  | none => simp [primStep, mirrorTable, mirrorPrim, hm, cons]
  | some mv =>
    cases hr : mv.right <;>
      simp [primStep, mirrorTable, mirrorPrim, hm, hr, cons, tail,
        cons_tail]

/-- The run relation is equivariant under reflection. -/
theorem run_mirror (M : Table) (n : Nat) (c : Prim) :
    run (mirrorTable M) n (mirrorPrim c) =
      (run M n c).map mirrorPrim := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    cases hs : primStep M c with
    | none => simp [run, primStep_mirror, hs]
    | some d => simp [run, primStep_mirror, hs, ih]

/-- Nonhalting of the direction-mirrored machine implies nonhalting of the
original machine, since the blank primitive configuration is reflection
invariant. -/
theorem never_of_mirror (M : Table)
    (h : ∀ n, ∃ c, run (mirrorTable M) n primBlank = some c) :
    ∀ n, ∃ c, run M n primBlank = some c := by
  intro n
  obtain ⟨c, hc⟩ := h n
  have hm :
      run (mirrorTable M) n primBlank =
        (run M n primBlank).map mirrorPrim := by
    simpa [mirrorPrim_blank] using run_mirror M n primBlank
  rw [hm] at hc
  cases hr : run M n primBlank with
  | none => simp [hr] at hc
  | some d => exact ⟨d, rfl⟩

end BB6BlockFAR
