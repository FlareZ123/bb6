import Junc744To924
import Low43C0Uniform
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 65536

namespace BB429Junc924To1008

open BB6Coverage BB6Bubble
open BB429OddExcursion BB429PhysicalFrontier BB429PhysicalBridge
open BB429PhysicalNoFatalConverse BB429JuncCanonical
open BB429Low42PhysicalNoFatalAnyHead BB429Low42PhysicalNoFatal
open BB429Low43UniformContinuation BB429Junc11Return32
open BB429Junc744To924 BB429OuterSafe BB429LowEven4k

private theorem compose_run {m n : Nat} {c d e : Config}
    (h₁ : run target429 m c = some d)
    (h₂ : run target429 n d = some e) :
    run target429 (m+n) c = some e :=
  physical_run_add_of_endpoint m n c d e h₁ h₂

/-- Arbitrary-head lift of the uniform low43 Junc-to-Junc theorem. -/
theorem low43_uniform_anyhead
    (v k : Nat) (hv : 1 ≤ v) (c : Config)
    (hrep : Represents (junc (v+2*k+2) 0 (2*v+1)) c) :
    ∃ d : Config,
      run target429 (4*v*v+22*v+38*k+174) c = some d ∧
      Represents (junc (2*k+9) 0 (4*v-2)) d ∧
      d.head = c.head + (6 - 2*(v : Int)) := by
  obtain ⟨d₀,hrun₀,hrep₀,hhead₀⟩ :=
    physical_low43_junc_to_junc v k hv
  have hcanon :
      c = translatedJ (v+2*k+2) (2*v+1) c.head :=
    represented_junc_eq_translatedJ (v+2*k+2) (2*v+1) c hrep
  have hshift :
      c = shiftConfig c.head (jConfig (v+2*k+2) (2*v+1)) := by
    calc
      c = translatedJ (v+2*k+2) (2*v+1) c.head := hcanon
      _ = shiftConfig c.head (jConfig (v+2*k+2) (2*v+1)) :=
        translatedJ_eq_shift (v+2*k+2) (2*v+1) c.head
  have hrun :
      run target429 (4*v*v+22*v+38*k+174) c =
        some (shiftConfig c.head d₀) := by
    calc
      run target429 (4*v*v+22*v+38*k+174) c =
          run target429 (4*v*v+22*v+38*k+174)
            (shiftConfig c.head (jConfig (v+2*k+2) (2*v+1))) := by
              rw [hshift]
      _ = (run target429 (4*v*v+22*v+38*k+174)
            (jConfig (v+2*k+2) (2*v+1))).map (shiftConfig c.head) :=
        shift_run c.head target429 (jConfig (v+2*k+2) (2*v+1))
          (4*v*v+22*v+38*k+174)
      _ = some (shiftConfig c.head d₀) := by simp [jConfig,hrun₀]
  have hrepD :
      Represents (junc (2*k+9) 0 (4*v-2)) (shiftConfig c.head d₀) := by
    apply (represented_junc_iff_translatedJ (2*k+9) (4*v-2) _).2
    calc
      shiftConfig c.head d₀ =
          shiftConfig c.head (translatedJ (2*k+9) (4*v-2) d₀.head) := by
            rw [represented_junc_eq_translatedJ (2*k+9) (4*v-2) d₀ hrep₀]
      _ = translatedJ (2*k+9) (4*v-2) (d₀.head+c.head) :=
        shift_translatedJ (2*k+9) (4*v-2) c.head d₀.head
      _ = translatedJ (2*k+9) (4*v-2) (shiftConfig c.head d₀).head := by
        simp [shiftConfig]
  have hhead : (shiftConfig c.head d₀).head =
      c.head + (6 - 2*(v : Int)) := by
    change d₀.head + c.head = c.head + (6 - 2*(v : Int))
    rw [hhead₀]
    omega
  exact ⟨shiftConfig c.head d₀,hrun,hrepD,hhead⟩

/-- Seven outer-safe returns take J(0,924) to J(381,183). -/
private theorem outer_ladder_924_to_381_183
    (c : Config) (hrep : Represents (junc 0 0 924) c) :
    ∃ d : Config,
      run target429 191493 c = some d ∧
      Represents (junc 381 0 183) d ∧
      d.head = c.head + 741 := by
  obtain ⟨c₁,h₁,r₁,hd₁⟩ :=
    outer_segment_physical_delta 0 0 924 c hrep (by omega)
  have r₁' : Represents (junc 3 0 921) c₁ := by simpa using r₁
  obtain ⟨c₂,h₂,r₂,hd₂⟩ :=
    outer_segment_physical_delta 3 0 921 c₁ r₁' (by omega)
  have r₂' : Represents (junc 9 0 912) c₂ := by simpa using r₂
  obtain ⟨c₃,h₃,r₃,hd₃⟩ :=
    outer_segment_physical_delta 9 0 912 c₂ r₂' (by omega)
  have r₃' : Represents (junc 21 0 891) c₃ := by simpa using r₃
  obtain ⟨c₄,h₄,r₄,hd₄⟩ :=
    outer_segment_physical_delta 21 0 891 c₃ r₃' (by omega)
  have r₄' : Represents (junc 45 0 846) c₄ := by simpa using r₄
  obtain ⟨c₅,h₅,r₅,hd₅⟩ :=
    outer_segment_physical_delta 45 0 846 c₄ r₄' (by omega)
  have r₅' : Represents (junc 93 0 753) c₅ := by simpa using r₅
  obtain ⟨c₆,h₆,r₆,hd₆⟩ :=
    outer_segment_physical_delta 93 0 753 c₅ r₅' (by omega)
  have r₆' : Represents (junc 189 0 564) c₆ := by simpa using r₆
  obtain ⟨c₇,h₇,r₇,hd₇⟩ :=
    outer_segment_physical_delta 189 0 564 c₆ r₆' (by omega)
  have h₁₂ := compose_run h₁ h₂
  have h₁₂₃ := compose_run h₁₂ h₃
  have h₁₂₃₄ := compose_run h₁₂₃ h₄
  have h₁₂₃₄₅ := compose_run h₁₂₃₄ h₅
  have h₁₂₃₄₅₆ := compose_run h₁₂₃₄₅ h₆
  have h₁₂₃₄₅₆₇ := compose_run h₁₂₃₄₅₆ h₇
  have htime :
      ((((((outerCost 0 0 + outerCost 3 0) + outerCost 9 0) +
        outerCost 21 0) + outerCost 45 0) + outerCost 93 0) +
        outerCost 189 0) = 191493 := by decide
  have hhead : c₇.head = c.head + 741 := by
    rw [hd₇,hd₆,hd₅,hd₄,hd₃,hd₂,hd₁]
    norm_num
  exact ⟨c₇,by simpa [htime] using h₁₂₃₄₅₆₇,by simpa using r₇,hhead⟩

/-- The concrete low-even 4k return J(297,362) -> J(11,954). -/
private theorem lowEven_181_58_physical
    (c : Config) (hrep : Represents (junc 297 0 362) c) :
    ∃ d : Config,
      run target429 136331 c = some d ∧
      Represents (junc 11 0 954) d ∧
      d.head = c.head - 585 := by
  obtain ⟨d,hrun,hrepD,hhead⟩ :=
    lowEven4k_prepared_return_physical 181 58 (by omega) c hrep
  have htime :
      juncPosFullTime 181 0 + (16*181+18*58+261) = 136331 := by
    norm_num [juncPosFullTime_formula]
  have hwidth : 4*181+4*58-2=954 := by norm_num
  have hhead' : d.head = c.head - 585 := by
    rw [hhead]
    norm_num
  exact ⟨d,by simpa [htime] using hrun,
    by simpa [hwidth] using hrepD,hhead'⟩

/-- Five outer-safe returns take J(11,954) to J(445,101). -/
private theorem outer_ladder_11_954_to_445_101
    (c : Config) (hrep : Represents (junc 11 0 954) c) :
    ∃ d : Config,
      run target429 261433 c = some d ∧
      Represents (junc 445 0 101) d ∧
      d.head = c.head + 853 := by
  obtain ⟨c₁,h₁,r₁,hd₁⟩ :=
    outer_segment_physical_delta 11 0 954 c hrep (by omega)
  have r₁' : Represents (junc 25 0 929) c₁ := by simpa using r₁
  obtain ⟨c₂,h₂,r₂,hd₂⟩ :=
    outer_segment_physical_delta 25 0 929 c₁ r₁' (by omega)
  have r₂' : Represents (junc 53 0 876) c₂ := by simpa using r₂
  obtain ⟨c₃,h₃,r₃,hd₃⟩ :=
    outer_segment_physical_delta 53 0 876 c₂ r₂' (by omega)
  have r₃' : Represents (junc 109 0 767) c₃ := by simpa using r₃
  obtain ⟨c₄,h₄,r₄,hd₄⟩ :=
    outer_segment_physical_delta 109 0 767 c₃ r₃' (by omega)
  have r₄' : Represents (junc 221 0 546) c₄ := by simpa using r₄
  obtain ⟨c₅,h₅,r₅,hd₅⟩ :=
    outer_segment_physical_delta 221 0 546 c₄ r₄' (by omega)
  have h₁₂ := compose_run h₁ h₂
  have h₁₂₃ := compose_run h₁₂ h₃
  have h₁₂₃₄ := compose_run h₁₂₃ h₄
  have h₁₂₃₄₅ := compose_run h₁₂₃₄ h₅
  have htime :
      ((((outerCost 11 0 + outerCost 25 0) + outerCost 53 0) +
        outerCost 109 0) + outerCost 221 0) = 261433 := by decide
  have hhead : c₅.head = c.head + 853 := by
    rw [hd₅,hd₄,hd₃,hd₂,hd₁]
    norm_num
  exact ⟨c₅,by simpa [htime] using h₁₂₃₄₅,by simpa using r₅,hhead⟩

/-- The full physical route J(0,924) -> J(0,1008), in 691,310
    primitive steps with net head displacement -64. -/
theorem junc0_924_to_junc0_1008_physical
    (c₉₂₄ : Config) (hrep₉₂₄ : Represents (junc 0 0 924) c₉₂₄) :
    ∃ c₁₀₀₈ : Config,
      run target429 691310 c₉₂₄ = some c₁₀₀₈ ∧
      Represents (junc 0 0 1008) c₁₀₀₈ ∧
      c₁₀₀₈.head = c₉₂₄.head - 64 ∧
      (∀ t : Nat, t ≤ 691310 →
        ∃ e : Config, run target429 t c₉₂₄ = some e ∧
          ¬ physicalC01 e) := by
  obtain ⟨c₃₈₁,houter,r₃₈₁,hdOuter⟩ :=
    outer_ladder_924_to_381_183 c₉₂₄ hrep₉₂₄
  obtain ⟨c₂₉₇,h43,r₂₉₇,hd43⟩ :=
    low43_uniform_anyhead 91 144 (by omega) c₃₈₁ r₃₈₁
  have h43Time : 4*91*91+22*91+38*144+174=40772 := by norm_num
  have h43' : run target429 40772 c₃₈₁ = some c₂₉₇ := by
    simpa [h43Time] using h43
  have r₂₉₇' : Represents (junc 297 0 362) c₂₉₇ := by
    simpa using r₂₉₇
  have hhead43' : c₂₉₇.head = c₃₈₁.head - 176 := by
    rw [hd43]
    norm_num

  obtain ⟨c₁₁₉₅₄,hEven,r₁₁₉₅₄,hheadEven⟩ :=
    lowEven_181_58_physical c₂₉₇ r₂₉₇'
  obtain ⟨c₄₄₅,houter₂,r₄₄₅,hdOuter₂⟩ :=
    outer_ladder_11_954_to_445_101 c₁₁₉₅₄ r₁₁₉₅₄
  obtain ⟨c₃₉₈,hodd,r₃₉₈,hheadOdd⟩ :=
    lowOdd_raw_head_any 50 196 c₄₄₅ r₄₄₅
  have hoddTime : 4*50*50+22*50+22*196+100=15512 := by norm_num
  have hodd' : run target429 15512 c₄₄₅ = some c₃₉₈ := by
    simpa [hoddTime] using hodd
  have r₃₉₈' : Represents (junc 398 0 202) c₃₉₈ := by
    simpa using r₃₉₈
  have hheadOdd' : c₃₉₈.head = c₄₄₅.head - 98 := by
    rw [hheadOdd]
    norm_num

  obtain ⟨c₁₀₀₈,h42,r₁₀₀₈,hhead42,_⟩ :=
    low42_raw_head_any_c01_free 101 148 c₃₉₈ r₃₉₈'
  have h42Time : 4*101*101+22*101+18*148+79=45769 := by norm_num
  have h42' : run target429 45769 c₃₉₈ = some c₁₀₀₈ := by
    simpa [h42Time] using h42
  have r₁₀₀₈' : Represents (junc 0 0 1008) c₁₀₀₈ := by
    simpa using r₁₀₀₈
  have hhead42' : c₁₀₀₈.head = c₃₉₈.head - 799 := by
    rw [hhead42]
    norm_num

  have h₁₂ := compose_run houter h43'
  have h₁₂₃ := compose_run h₁₂ hEven
  have h₁₂₃₄ := compose_run h₁₂₃ houter₂
  have h₁₂₃₄₅ := compose_run h₁₂₃₄ hodd'
  have h₁₂₃₄₅₆ := compose_run h₁₂₃₄₅ h42'
  have htime :
      ((((((191493+40772)+136331)+261433)+15512)+45769) =
        691310) := by norm_num
  have hrun : run target429 691310 c₉₂₄ = some c₁₀₀₈ := by
    simpa [htime] using h₁₂₃₄₅₆
  have hhead : c₁₀₀₈.head = c₉₂₄.head - 64 := by
    rw [hhead42',hheadOdd',hdOuter₂,hheadEven,hhead43',hdOuter]
    omega
  have hfree := junc0_physical_c01_free 0 1008 c₁₀₀₈ r₁₀₀₈'
  have hlive := junc0_physical_live 0 1008 c₁₀₀₈ r₁₀₀₈'
  have hprefix :=
    physical_run_prefix_c01_free 691310 c₉₂₄ c₁₀₀₈ hrun hfree hlive
  exact ⟨c₁₀₀₈,hrun,r₁₀₀₈',hhead,hprefix⟩

/-- Blank-root extension through J(0,1008), at step 3,363,397. -/
theorem blank_root_to_junc0_1008 :
    ∃ c₉₂₄ c₁₀₀₈ : Config,
      run target429 2672087 blank = some c₉₂₄ ∧
      Represents (junc 0 0 924) c₉₂₄ ∧
      run target429 691310 c₉₂₄ = some c₁₀₀₈ ∧
      Represents (junc 0 0 1008) c₁₀₀₈ ∧
      c₁₀₀₈.head = c₉₂₄.head - 64 ∧
      run target429 3363397 blank = some c₁₀₀₈ ∧
      (∀ t : Nat, t ≤ 3363397 →
        ∃ e : Config, run target429 t blank = some e ∧
          ¬ physicalC01 e) := by
  obtain ⟨c₉₂₄,hroot,hrep₉₂₄,_⟩ :=
    blank_root_to_junc0_924
  obtain ⟨c₁₀₀₈,hroute,hrep₁₀₀₈,hheadRoute,_⟩ :=
    junc0_924_to_junc0_1008_physical c₉₂₄ hrep₉₂₄
  have htotal := compose_run hroot hroute
  have htime : 2672087+691310=3363397 := by norm_num
  have hrun : run target429 3363397 blank = some c₁₀₀₈ := by
    simpa [htime] using htotal
  have hfree := junc0_physical_c01_free 0 1008 c₁₀₀₈ hrep₁₀₀₈
  have hlive := junc0_physical_live 0 1008 c₁₀₀₈ hrep₁₀₀₈
  have hprefix :=
    physical_run_prefix_c01_free 3363397 blank c₁₀₀₈ hrun hfree hlive
  exact ⟨c₉₂₄,c₁₀₀₈,hroot,hrep₉₂₄,hroute,hrep₁₀₀₈,hheadRoute,
    hrun,hprefix⟩

#print axioms junc0_924_to_junc0_1008_physical
#print axioms blank_root_to_junc0_1008

end BB429Junc924To1008
