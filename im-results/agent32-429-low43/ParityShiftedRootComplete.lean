import Low43BlankRootExtension
import Low43ParityShift
import ParityShiftedReturns
import JuncCanonical
import RootShift
import PhysicalNoFatalConverse
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 65536

namespace BB429ParityShiftedRootComplete

open BB6Coverage BB6Bubble
open BB429PhysicalFrontier BB429PhysicalBridge
open BB429OddExcursion BB429JPhysical BB429JuncCanonical
open BB429DeltaPhysicalBridge BB429PhysicalNoFatalConverse
open BB429ParityShiftedEntry BB429ParityShiftedReturns
open BB429Low43BlankRootExtension BB429LowEvenR32RootExtension
open BB429JuncHeadExcursion

private theorem composeDelta
    {n m : Nat} {z₀ z₁ z₂ : Zipper} {d₁ d₂ : Int}
    (h₁ : runWithDelta n z₀ = some (z₁, d₁))
    (h₂ : runWithDelta m z₁ = some (z₂, d₂)) :
    runWithDelta (n+m) z₀ = some (z₂, d₁+d₂) := by
  rw [runWithDelta_add, h₁]
  simp [h₂]

/-- The five ordinary Junc normalizations from J(0,344) to J(93,173).
    This is the exact source-level outer ladder, with total displacement +171. -/
theorem junc0_344_to_junc93_173_delta :
    runWithDelta 11139 (junc 0 0 344) =
      some (junc 93 0 173, 171) := by
  have h0 : runWithDelta 27 (junc 0 0 344) =
      some (junc 3 0 341, 3) := by
    simpa [juncNormalizeTime, juncPosFullTime] using
      (juncNormalize_delta 0 0 344 (by omega))
  have h1 : runWithDelta 93 (junc 3 0 341) =
      some (junc 9 0 332, 9) := by
    simpa [juncNormalizeTime, juncPosFullTime] using
      (juncNormalize_delta 3 0 341 (by omega))
  have h2 : runWithDelta 441 (junc 9 0 332) =
      some (junc 21 0 311, 21) := by
    simpa [juncNormalizeTime, juncPosFullTime] using
      (juncNormalize_delta 9 0 332 (by omega))
  have h3 : runWithDelta 2001 (junc 21 0 311) =
      some (junc 45 0 266, 45) := by
    simpa [juncNormalizeTime, juncPosFullTime] using
      (juncNormalize_delta 21 0 311 (by omega))
  have h4 : runWithDelta 8577 (junc 45 0 266) =
      some (junc 93 0 173, 93) := by
    simpa [juncNormalizeTime, juncPosFullTime] using
      (juncNormalize_delta 45 0 266 (by omega))
  have h01 : runWithDelta 120 (junc 0 0 344) =
      some (junc 9 0 332, 12) := by
    simpa using composeDelta h0 h1
  have h012 : runWithDelta 561 (junc 0 0 344) =
      some (junc 21 0 311, 33) := by
    simpa using composeDelta h01 h2
  have h0123 : runWithDelta 2562 (junc 0 0 344) =
      some (junc 45 0 266, 78) := by
    simpa using composeDelta h012 h3
  simpa using composeDelta h0123 h4

/-- Translation preserves a complete zipper representation. -/
private theorem shift_represents (z : Zipper) (c : Config) (j : Int)
    (h : Represents z c) :
    Represents z (shiftConfig j c) := by
  rcases h with ⟨hs, hc, hl, hr⟩
  refine ⟨hs, ?_, ?_, ?_⟩
  · change c.tape (c.head+j-j) = z.current
    have heq : c.head+j-j = c.head := by omega
    rw [heq]
    exact hc
  · intro k
    change c.tape ((c.head+j)-((k:Int)+1)-j) = z.left.getD k false
    have heq : (c.head+j)-((k:Int)+1)-j = c.head-((k:Int)+1) := by omega
    rw [heq]
    exact hl k
  · intro k
    change c.tape ((c.head+j)+((k:Int)+1)-j) = z.right.getD k false
    have heq : (c.head+j)+((k:Int)+1)-j = c.head+((k:Int)+1) := by omega
    rw [heq]
    exact hr k

/-- Compose physical runs while retaining the all-prefix exclusion of the
    actual C/01 halting gateway. -/
private theorem physical_prefix_compose
    (m n : Nat) (c c₁ c₂ : Config)
    (h₁ : run target429 m c = some c₁)
    (h₂ : run target429 n c₁ = some c₂)
    (hp₁ : ∀ t : Nat, t ≤ m →
      ∃ e : Config, run target429 t c = some e ∧ ¬ physicalC01 e)
    (hp₂ : ∀ t : Nat, t ≤ n →
      ∃ e : Config, run target429 t c₁ = some e ∧ ¬ physicalC01 e) :
    run target429 (m+n) c = some c₂ ∧
    (∀ t : Nat, t ≤ m+n →
      ∃ e : Config, run target429 t c = some e ∧ ¬ physicalC01 e) := by
  have htotal :=
    physical_run_add_of_endpoint m n c c₁ c₂ h₁ h₂
  refine ⟨htotal, ?_⟩
  intro t ht
  by_cases hfirst : t ≤ m
  · exact hp₁ t hfirst
  · let s : Nat := t-m
    have hs : s ≤ n := by dsimp [s]; omega
    obtain ⟨e, he, hsafe⟩ := hp₂ s hs
    have htime : t = m+s := by dsimp [s]; omega
    refine ⟨e, ?_, hsafe⟩
    rw [htime, physical_run_add, h₁]
    exact he

private theorem live_A_state (c : Config)
    (hstate : c.state = (⟨0, by decide⟩ : Fin 6)) :
    rawStep target429 c ≠ none := by
  have hA0 : target429 ((⟨0, by decide⟩ : Fin 6), false) =
      some ⟨true, true, ⟨1, by decide⟩⟩ := by decide
  have hA1 : target429 ((⟨0, by decide⟩ : Fin 6), true) =
      some ⟨false, false, ⟨5, by decide⟩⟩ := by decide
  cases hb : c.tape c.head with
  | false =>
      have hread : readSlot c = ((⟨0, by decide⟩ : Fin 6), false) := by
        simp [readSlot, hstate, hb]
      simp [rawStep, hread, hA0]
  | true =>
      have hread : readSlot c = ((⟨0, by decide⟩ : Fin 6), true) := by
        simp [readSlot, hstate, hb]
      simp [rawStep, hread, hA1]

/-- Starting from any complete physical representation of J(0,344), the
    original table reaches J(0,408) in exactly 145,374 steps.  The proof
    composes the 11,139-step outer ladder, the 31,154-step parity-shifted
    low43 entry, and the 103,081-step return.  Every primitive prefix avoids
    the C/01 halting gateway. -/
theorem junc0_344_to_junc0_408_physical
    (c₃₄₄ : Config) (hrep₃₄₄ : Represents (junc 0 0 344) c₃₄₄) :
    ∃ c₄₀₈ : Config,
      run target429 145374 c₃₄₄ = some c₄₀₈ ∧
      Represents (junc 0 0 408) c₄₀₈ ∧
      c₄₀₈.head = c₃₄₄.head - 48 ∧
      (∀ t : Nat, t ≤ 145374 →
        ∃ e : Config, run target429 t c₃₄₄ = some e ∧ ¬ physicalC01 e) := by
  obtain ⟨c₉₃, houter, hrep₉₃, hhead₉₃⟩ :=
    source_runWithDelta_rep 11139 (junc 0 0 344) c₃₄₄ hrep₃₄₄
      (junc 93 0 173) 171 junc0_344_to_junc93_173_delta

  have hstate₉₃val : c₉₃.state.val = 0 := by
    simpa [junc, z] using hrep₉₃.1
  have hstate₉₃ : c₉₃.state = (⟨0, by decide⟩ : Fin 6) := by
    exact Fin.ext hstate₉₃val
  have hfree₉₃ : ¬ physicalC01 c₉₃ := by
    simp [physicalC01, hstate₉₃val]
  have hlive₉₃ : rawStep target429 c₉₃ ≠ none :=
    live_A_state c₉₃ hstate₉₃
  have hpouter :=
    physical_run_prefix_c01_free 11139 c₃₄₄ c₉₃ houter hfree₉₃ hlive₉₃

  obtain ⟨cC, hentry, hheadC, hrepC⟩ :=
    junc93_173_to_shiftedC0
  let canonical₉₃ : Config :=
    {state := A, head := 0, tape := fun x => jTape 93 173 x}
  have htranslated :=
    represented_junc_eq_translatedJ 93 173 c₉₃ hrep₉₃
  have hshiftStart :
      shiftConfig c₉₃.head canonical₉₃ = c₉₃ := by
    calc
      shiftConfig c₉₃.head canonical₉₃ =
          translatedJ 93 173 c₉₃.head := rfl
      _ = c₉₃ := htranslated.symm
  have hentryShift :
      run target429 31154 c₉₃ = some (shiftConfig c₉₃.head cC) := by
    calc
      run target429 31154 c₉₃ =
          run target429 31154 (shiftConfig c₉₃.head canonical₉₃) := by
            rw [← hshiftStart]
      _ = (run target429 31154 canonical₉₃).map
          (shiftConfig c₉₃.head) :=
            shift_run c₉₃.head target429 canonical₉₃ 31154
      _ = some (shiftConfig c₉₃.head cC) := by
            have hentry' : run target429 31154 canonical₉₃ = some cC := by
              simpa [canonical₉₃] using hentry
            rw [hentry']
            rfl
  have hrepCShift :
      Represents shiftedC0 (shiftConfig c₉₃.head cC) :=
    shift_represents shiftedC0 cC c₉₃.head hrepC

  have hstateC : (shiftConfig c₉₃.head cC).state.val = 2 := by
    simpa [shiftedC0, z] using hrepCShift.1
  have hcurC : (shiftConfig c₉₃.head cC).tape
      (shiftConfig c₉₃.head cC).head = false := by
    simpa [shiftedC0, z] using hrepCShift.2.1
  have hrightC : (shiftConfig c₉₃.head cC).tape
      ((shiftConfig c₉₃.head cC).head+1) = false := by
    have hr := hrepCShift.2.2.2 0
    simpa [shiftedC0, z] using hr
  have hpentry :=
    physical_run_prefix_c01_free_of_c0_blank_right
      31154 c₉₃ (shiftConfig c₉₃.head cC) hentryShift hstateC hcurC hrightC

  have hdeltaCont :
      runWithDelta 103081 shiftedC0 =
        some (junc 0 0 408, -397) := by
    simpa [shiftedC0, parityShiftedC0] using
      parityShiftedC0_to_junc0_408
  obtain ⟨c₄₀₈, hcont, hrep₄₀₈, hheadCont⟩ :=
    source_runWithDelta_rep 103081 shiftedC0
      (shiftConfig c₉₃.head cC) hrepCShift
      (junc 0 0 408) (-397) hdeltaCont

  have hstate₄₀₈val : c₄₀₈.state.val = 0 := by
    simpa [junc, z] using hrep₄₀₈.1
  have hstate₄₀₈ : c₄₀₈.state = (⟨0, by decide⟩ : Fin 6) := by
    exact Fin.ext hstate₄₀₈val
  have hfree₄₀₈ : ¬ physicalC01 c₄₀₈ := by
    simp [physicalC01, hstate₄₀₈val]
  have hlive₄₀₈ : rawStep target429 c₄₀₈ ≠ none :=
    live_A_state c₄₀₈ hstate₄₀₈
  have hpcont :=
    physical_run_prefix_c01_free 103081
      (shiftConfig c₉₃.head cC) c₄₀₈ hcont hfree₄₀₈ hlive₄₀₈

  have chain₁ := physical_prefix_compose
    11139 31154 c₃₄₄ c₉₃ (shiftConfig c₉₃.head cC)
    houter hentryShift hpouter hpentry
  have chain₂ := physical_prefix_compose
    (11139+31154) 103081 c₃₄₄ (shiftConfig c₉₃.head cC) c₄₀₈
    chain₁.1 hcont chain₁.2 hpcont

  have hshiftHead : (shiftConfig c₉₃.head cC).head =
      c₉₃.head + 178 := by
    change cC.head + c₉₃.head = c₉₃.head + 178
    rw [hheadC]
    omega
  have hheadFinal : c₄₀₈.head = c₃₄₄.head - 48 := by
    calc
      c₄₀₈.head = (shiftConfig c₉₃.head cC).head + (-397) := hheadCont
      _ = c₉₃.head + 178 - 397 := by simpa [hshiftHead]
      _ = c₃₄₄.head - 48 := by omega
  have htime : 11139+31154+103081=145374 := by norm_num
  refine ⟨c₄₀₈, ?_, hrep₄₀₈, hheadFinal, ?_⟩
  · simpa [htime] using chain₂.1
  · simpa [htime] using chain₂.2

/-- The authentic blank A-root has a 314,966-step physical prefix to
    J(0,408).  It extends the 169,592-step blank-root prefix to J(0,344)
    by the preceding 145,374-step complete-tape return.  Every primitive
    prefix of the combined run avoids the C/01 halting gateway. -/
theorem blank_root_to_junc0_408 :
    ∃ c₃₄₄ c₄₀₈ : Config,
      run target429 169592 blank = some c₃₄₄ ∧
      Represents (junc 0 0 344) c₃₄₄ ∧
      run target429 314966 blank = some c₄₀₈ ∧
      Represents (junc 0 0 408) c₄₀₈ ∧
      c₄₀₈.head = c₃₄₄.head - 48 ∧
      (∀ t : Nat, t ≤ 314966 →
        ∃ e : Config, run target429 t blank = some e ∧ ¬ physicalC01 e) := by
  obtain ⟨c₆₉, c₁₄₁, c₁₂₂, c₃₄₄,
      _, _, _, _, _, _, hroot, hrep₃₄₄, hprefixRoot⟩ :=
    blank_root_lowEvenR32_to_junc0_344
  obtain ⟨c₄₀₈, hreturn, hrep₄₀₈, hhead, hprefixReturn⟩ :=
    junc0_344_to_junc0_408_physical c₃₄₄ hrep₃₄₄
  have hprefixRoot' :
      ∀ t : Nat, t ≤ 169592 →
        ∃ e : Config, run target429 t blank = some e ∧ ¬ physicalC01 e := by
    intro t ht
    obtain ⟨e, he, hsafe⟩ := hprefixRoot t ht
    have hsafe' : ¬
        (e.state.val = 2 ∧ e.tape e.head = false ∧
          e.tape (e.head+1) = true) := by
      change ¬
        (e.state.val = 2 ∧ e.tape e.head = false ∧
          e.tape (e.head+1) = true) at hsafe
      exact hsafe
    exact ⟨e, he, hsafe'⟩
  have hcombined := physical_prefix_compose
    169592 145374 blank c₃₄₄ c₄₀₈ hroot hreturn
    hprefixRoot' hprefixReturn
  have htime : 169592+145374=314966 := by norm_num
  refine ⟨c₃₄₄,c₄₀₈,hroot,hrep₃₄₄,?_,hrep₄₀₈,hhead,?_⟩
  · simpa [htime] using hcombined.1
  · simpa [htime] using hcombined.2

#print axioms junc0_344_to_junc93_173_delta
#print axioms shift_represents
#print axioms junc0_344_to_junc0_408_physical
#print axioms blank_root_to_junc0_408

end BB429ParityShiftedRootComplete
