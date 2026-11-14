import Junc0ReturnMap28RootChain
import Junc11Return32
import Low43C0_1_189
import LowOddPhysical
import Low42PhysicalNoFatalAnyHead
import PhysicalNoFatalConverse
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 65536

namespace BB429Junc744To924

open BB6Coverage BB6Bubble
open BB429OddExcursion BB429PhysicalFrontier BB429PhysicalBridge
open BB429DeltaPhysicalBridge BB429PhysicalNoFatalConverse
open BB429Low43C0_1_189 BB429LowOddPhysical
open BB429Low42PhysicalNoFatalAnyHead BB429Low42PhysicalNoFatal
open BB429JuncCanonical BB429Junc0ReturnMap28RootChain
open BB429Junc11Return32

private theorem compose_run {m n : Nat} {c d e : Config}
    (h₁ : run target429 m c = some d)
    (h₂ : run target429 n d = some e) :
    run target429 (m+n) c = some e :=
  physical_run_add_of_endpoint m n c d e h₁ h₂

/-- The seven outer-safe returns 0 -> 3 -> 9 -> 21 -> 45 -> 93
    -> 189 -> 381. This consumes 741 units of right budget, takes
    191,493 primitive steps, and moves the head right by 741. -/
private theorem outer_ladder_744_to_381_3
    (c : Config) (hrep : Represents (junc 0 0 744) c) :
    ∃ d : Config,
      run target429 191493 c = some d ∧
      Represents (junc 381 0 3) d ∧
      d.head = c.head + 741 := by
  obtain ⟨c₁,h₁,r₁,hd₁⟩ :=
    outer_segment_physical_delta 0 0 744 c hrep (by omega)
  have r₁' : Represents (junc 3 0 741) c₁ := by simpa using r₁
  obtain ⟨c₂,h₂,r₂,hd₂⟩ :=
    outer_segment_physical_delta 3 0 741 c₁ r₁' (by omega)
  have r₂' : Represents (junc 9 0 732) c₂ := by simpa using r₂
  obtain ⟨c₃,h₃,r₃,hd₃⟩ :=
    outer_segment_physical_delta 9 0 732 c₂ r₂' (by omega)
  have r₃' : Represents (junc 21 0 711) c₃ := by simpa using r₃
  obtain ⟨c₄,h₄,r₄,hd₄⟩ :=
    outer_segment_physical_delta 21 0 711 c₃ r₃' (by omega)
  have r₄' : Represents (junc 45 0 666) c₄ := by simpa using r₄
  obtain ⟨c₅,h₅,r₅,hd₅⟩ :=
    outer_segment_physical_delta 45 0 666 c₄ r₄' (by omega)
  have r₅' : Represents (junc 93 0 573) c₅ := by simpa using r₅
  obtain ⟨c₆,h₆,r₆,hd₆⟩ :=
    outer_segment_physical_delta 93 0 573 c₅ r₅' (by omega)
  have r₆' : Represents (junc 189 0 384) c₆ := by simpa using r₆
  obtain ⟨c₇,h₇,r₇,hd₇⟩ :=
    outer_segment_physical_delta 189 0 384 c₆ r₆' (by omega)
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
  exact ⟨c₇, by simpa [htime] using h₁₂₃₄₅₆₇, by simpa using r₇, hhead⟩

/-- The five outer-safe returns 11 -> 25 -> 53 -> 109 -> 221
    -> 445. This takes 261,433 steps, consumes 853 units of right
    budget, and moves the head right by 853. -/
private theorem outer_ladder_11_870_to_445_17
    (c : Config) (hrep : Represents (junc 11 0 870) c) :
    ∃ d : Config,
      run target429 261433 c = some d ∧
      Represents (junc 445 0 17) d ∧
      d.head = c.head + 853 := by
  obtain ⟨c₁,h₁,r₁,hd₁⟩ :=
    outer_segment_physical_delta 11 0 870 c hrep (by omega)
  have r₁' : Represents (junc 25 0 845) c₁ := by simpa using r₁
  obtain ⟨c₂,h₂,r₂,hd₂⟩ :=
    outer_segment_physical_delta 25 0 845 c₁ r₁' (by omega)
  have r₂' : Represents (junc 53 0 792) c₂ := by simpa using r₂
  obtain ⟨c₃,h₃,r₃,hd₃⟩ :=
    outer_segment_physical_delta 53 0 792 c₂ r₂' (by omega)
  have r₃' : Represents (junc 109 0 683) c₃ := by simpa using r₃
  obtain ⟨c₄,h₄,r₄,hd₄⟩ :=
    outer_segment_physical_delta 109 0 683 c₃ r₃' (by omega)
  have r₄' : Represents (junc 221 0 462) c₄ := by simpa using r₄
  obtain ⟨c₅,h₅,r₅,hd₅⟩ :=
    outer_segment_physical_delta 221 0 462 c₄ r₄' (by omega)
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
  exact ⟨c₅, by simpa [htime] using h₁₂₃₄₅, by simpa using r₅, hhead⟩

/-- Lift the canonical 7,382-step low43 gap to every physical
    configuration representing J(381,3). -/
private theorem low43_gap_anyhead
    (c : Config) (hrep : Represents (junc 381 0 3) c) :
    ∃ d : Config,
      run target429 7382 c = some d ∧
      Represents (junc 387 0 2) d ∧
      d.head = c.head + 4 := by
  obtain ⟨d₀,hrun₀,hrep₀,hhead₀,_⟩ :=
    junc381_3_to_junc387_2_physical
  have hcanon :
      c = translatedJ 381 3 c.head :=
    represented_junc_eq_translatedJ 381 3 c hrep
  have hshift :
      c = shiftConfig c.head (jConfig 381 3) := by
    calc
      c = translatedJ 381 3 c.head := hcanon
      _ = shiftConfig c.head (jConfig 381 3) :=
        translatedJ_eq_shift 381 3 c.head
  have hrun :
      run target429 7382 c = some (shiftConfig c.head d₀) := by
    calc
      run target429 7382 c =
          run target429 7382 (shiftConfig c.head (jConfig 381 3)) := by
            rw [hshift]
      _ = (run target429 7382 (jConfig 381 3)).map (shiftConfig c.head) :=
        shift_run c.head target429 (jConfig 381 3) 7382
      _ = some (shiftConfig c.head d₀) := by simp [jConfig,hrun₀]
  have hrepD :
      Represents (junc 387 0 2) (shiftConfig c.head d₀) := by
    apply (represented_junc_iff_translatedJ 387 2 _).2
    calc
      shiftConfig c.head d₀ =
          shiftConfig c.head (translatedJ 387 2 d₀.head) := by
            rw [represented_junc_eq_translatedJ 387 2 d₀ hrep₀]
      _ = translatedJ 387 2 (d₀.head+c.head) :=
        shift_translatedJ 387 2 c.head d₀.head
      _ = translatedJ 387 2 (shiftConfig c.head d₀).head := by
        simp [shiftConfig]
  have hhead : (shiftConfig c.head d₀).head = c.head + 4 := by
    change d₀.head + c.head = c.head + 4
    rw [hhead₀]
    omega
  exact ⟨shiftConfig c.head d₀, hrun, hrepD, hhead⟩

/-- Lift the low-odd canonical physical run to any complete physical
    configuration representing its Junc input. -/
private theorem lowOdd_raw_head_any
    (v n : Nat) (c : Config)
    (hrep : Represents (junc (v+2*n+3) 0 (2*v+1)) c) :
    ∃ d : Config,
      run target429 (4*v*v+22*v+22*n+100) c = some d ∧
      Represents (junc (2*n+6) 0 (4*v+2)) d ∧
      d.head = c.head + (2 - ((2*v : Nat) : Int)) := by
  obtain ⟨d₀,hrun₀,hrep₀,hhead₀⟩ := lowOdd_raw_head v n
  have hcanon :
      c = translatedJ (v+2*n+3) (2*v+1) c.head :=
    represented_junc_eq_translatedJ (v+2*n+3) (2*v+1) c hrep
  have hshift :
      c = shiftConfig c.head (jConfig (v+2*n+3) (2*v+1)) := by
    calc
      c = translatedJ (v+2*n+3) (2*v+1) c.head := hcanon
      _ = shiftConfig c.head (jConfig (v+2*n+3) (2*v+1)) :=
        translatedJ_eq_shift (v+2*n+3) (2*v+1) c.head
  have hrun :
      run target429 (4*v*v+22*v+22*n+100) c =
        some (shiftConfig c.head d₀) := by
    calc
      run target429 (4*v*v+22*v+22*n+100) c =
          run target429 (4*v*v+22*v+22*n+100)
            (shiftConfig c.head (jConfig (v+2*n+3) (2*v+1))) := by
              rw [hshift]
      _ = (run target429 (4*v*v+22*v+22*n+100)
            (jConfig (v+2*n+3) (2*v+1))).map (shiftConfig c.head) :=
          shift_run c.head target429 (jConfig (v+2*n+3) (2*v+1))
            (4*v*v+22*v+22*n+100)
      _ = some (shiftConfig c.head d₀) := by simp [jConfig,hrun₀]
  have hrepD :
      Represents (junc (2*n+6) 0 (4*v+2)) (shiftConfig c.head d₀) := by
    apply (represented_junc_iff_translatedJ (2*n+6) (4*v+2) _).2
    calc
      shiftConfig c.head d₀ =
          shiftConfig c.head (translatedJ (2*n+6) (4*v+2) d₀.head) := by
            rw [represented_junc_eq_translatedJ (2*n+6) (4*v+2) d₀ hrep₀]
      _ = translatedJ (2*n+6) (4*v+2) (d₀.head+c.head) :=
        shift_translatedJ (2*n+6) (4*v+2) c.head d₀.head
      _ = translatedJ (2*n+6) (4*v+2) (shiftConfig c.head d₀).head := by
        simp [shiftConfig]
  have hhead : (shiftConfig c.head d₀).head =
      c.head + (2 - ((2*v : Nat) : Int)) := by
    change d₀.head + c.head = c.head + (2 - ((2*v : Nat) : Int))
    rw [hhead₀]
    omega
  exact ⟨shiftConfig c.head d₀, hrun, hrepD, hhead⟩

/-- The complete physical route J(0,744) -> J(0,924), assembled from
    outer-safe ladders, the low43 gap, the low-even 4k return, three
    +32 J(11,w) cycles, the low-odd return, and the low42 return.

    Exact segment costs: 191493 + 7382 + 3761 + 683267 + 261433
    + 5306 + 5407 = 1,158,049. The total head displacement is -139.
    Since the endpoint is a live Junc state, the physical C/01 converse
    certifies every primitive prefix as nonfatal. -/
theorem junc0_744_to_junc0_924_physical
    (c₇₄₄ : Config) (hrep₇₄₄ : Represents (junc 0 0 744) c₇₄₄) :
    ∃ c₉₂₄ : Config,
      run target429 1158049 c₇₄₄ = some c₉₂₄ ∧
      Represents (junc 0 0 924) c₉₂₄ ∧
      c₉₂₄.head = c₇₄₄.head - 139 ∧
      (∀ t : Nat, t ≤ 1158049 →
        ∃ e : Config, run target429 t c₇₄₄ = some e ∧
          ¬ physicalC01 e) := by
  obtain ⟨c₃₈₁,houter,r₃₈₁,hdOuter⟩ :=
    outer_ladder_744_to_381_3 c₇₄₄ hrep₇₄₄
  obtain ⟨c₃₈₇,hgap,r₃₈₇,hdGap⟩ :=
    low43_gap_anyhead c₃₈₁ r₃₈₁
  obtain ⟨c₇₇₄,hEven,r₇₇₄,hheadEven⟩ :=
    lowEven4k_prepared_return_physical 1 193 (by omega) c₃₈₇ r₃₈₇
  have hEvenTime :
      juncPosFullTime 1 0 + (16*1+18*193+261) = 3761 := by
    norm_num [juncPosFullTime]
  have hEven' : run target429 3761 c₃₈₇ = some c₇₇₄ := by
    simpa [hEvenTime] using hEven
  have r₇₇₄' : Represents (junc 11 0 774) c₇₇₄ := by
    simpa using r₇₇₄
  have hheadEven' : c₇₇₄.head = c₃₈₇.head - 765 := by
    rw [hheadEven]
    norm_num

  obtain ⟨c₈₀₆,hcycle₁,r₈₀₆,hheadCycle₁⟩ :=
    junc11_lowEven_return32_physical 183 19 (by norm_num) (by norm_num)
      c₇₇₄ (by simpa using r₇₇₄')
  have hcycle₁' : run target429 202417 c₇₇₄ = some c₈₀₆ := by
    have ht : junc11Return32Cost 183 19 = 202417 := by
      norm_num [junc11Return32Cost]
    simpa [ht] using hcycle₁
  have r₈₀₆' : Represents (junc 11 0 806) c₈₀₆ := by
    simpa using r₈₀₆

  obtain ⟨c₈₃₈,hcycle₂,r₈₃₈,hheadCycle₂⟩ :=
    junc11_lowEven_return32_physical 199 11 (by norm_num) (by norm_num)
      c₈₀₆ (by simpa using r₈₀₆')
  have hcycle₂' : run target429 227073 c₈₀₆ = some c₈₃₈ := by
    have ht : junc11Return32Cost 199 11 = 227073 := by
      norm_num [junc11Return32Cost]
    simpa [ht] using hcycle₂
  have r₈₃₈' : Represents (junc 11 0 838) c₈₃₈ := by
    simpa using r₈₃₈

  obtain ⟨c₈₇₀,hcycle₃,r₈₇₀,hheadCycle₃⟩ :=
    junc11_lowEven_return32_physical 215 3 (by norm_num) (by norm_num)
      c₈₃₈ (by simpa using r₈₃₈')
  have hcycle₃' : run target429 253777 c₈₃₈ = some c₈₇₀ := by
    have ht : junc11Return32Cost 215 3 = 253777 := by
      norm_num [junc11Return32Cost]
    simpa [ht] using hcycle₃
  have r₈₇₀' : Represents (junc 11 0 870) c₈₇₀ := by
    simpa using r₈₇₀
  have hcycles₁₂ := compose_run hcycle₁' hcycle₂'
  have hcycles := compose_run hcycles₁₂ hcycle₃'
  have hcyclesTime : (202417+227073)+253777=683267 := by norm_num
  have hcycles' : run target429 683267 c₇₇₄ = some c₈₇₀ := by
    simpa [hcyclesTime] using hcycles
  have hheadCycles : c₈₇₀.head = c₇₇₄.head - 75 := by
    rw [hheadCycle₃,hheadCycle₂,hheadCycle₁]
    omega

  obtain ⟨c₄₄₅,houter₂,r₄₄₅,hdOuter₂⟩ :=
    outer_ladder_11_870_to_445_17 c₈₇₀ r₈₇₀'
  obtain ⟨c₄₄₀,hodd,r₄₄₀,hheadOdd⟩ :=
    lowOdd_raw_head_any 8 217 c₄₄₅ r₄₄₅
  have hoddTime : 4*8*8+22*8+22*217+100=5306 := by norm_num
  have hodd' : run target429 5306 c₄₄₅ = some c₄₄₀ := by
    simpa [hoddTime] using hodd
  have r₄₄₀' : Represents (junc 440 0 34) c₄₄₀ := by
    simpa using r₄₄₀
  have hheadOdd' : c₄₄₀.head = c₄₄₅.head - 14 := by
    rw [hheadOdd]
    norm_num

  obtain ⟨c₉₂₄,h42,r₉₂₄,hhead42,_⟩ :=
    low42_raw_head_any_c01_free 17 211 c₄₄₀ r₄₄₀'
  have h42Time : 4*17*17+22*17+18*211+79=5407 := by norm_num
  have h42' : run target429 5407 c₄₄₀ = some c₉₂₄ := by
    simpa [h42Time] using h42
  have r₉₂₄' : Represents (junc 0 0 924) c₉₂₄ := by
    simpa using r₉₂₄
  have hhead42' : c₉₂₄.head = c₄₄₀.head - 883 := by
    rw [hhead42]
    norm_num

  have h₁₂ := compose_run houter hgap
  have h₁₂₃ := compose_run h₁₂ hEven'
  have h₁₂₃₄ := compose_run h₁₂₃ hcycles'
  have h₁₂₃₄₅ := compose_run h₁₂₃₄ houter₂
  have h₁₂₃₄₅₆ := compose_run h₁₂₃₄₅ hodd'
  have h₁₂₃₄₅₆₇ := compose_run h₁₂₃₄₅₆ h42'
  have htime :
      (((((((191493+7382)+3761)+683267)+261433)+5306)+5407) =
        1158049) := by norm_num
  have hrun : run target429 1158049 c₇₄₄ = some c₉₂₄ := by
    simpa [htime] using h₁₂₃₄₅₆₇
  have hhead : c₉₂₄.head = c₇₄₄.head - 139 := by
    rw [hhead42',hheadOdd',hdOuter₂,hheadCycles,hheadEven',hdGap,hdOuter]
    omega
  have hfree := junc0_physical_c01_free 0 924 c₉₂₄ r₉₂₄'
  have hlive := junc0_physical_live 0 924 c₉₂₄ r₉₂₄'
  have hprefix :=
    physical_run_prefix_c01_free 1158049 c₇₄₄ c₉₂₄ hrun hfree hlive
  exact ⟨c₉₂₄,hrun,r₉₂₄',hhead,hprefix⟩

/-- The blank-root #429 prefix now reaches J(0,924) in 2,672,087
    primitive steps. The final live Junc endpoint certifies C/01-freedom
    of every primitive prefix of the entire blank-root run. -/
theorem blank_root_to_junc0_924 :
    ∃ c₉₂₄ : Config,
      run target429 2672087 blank = some c₉₂₄ ∧
      Represents (junc 0 0 924) c₉₂₄ ∧
      (∀ t : Nat, t ≤ 2672087 →
        ∃ e : Config, run target429 t blank = some e ∧
          ¬ physicalC01 e) := by
  obtain ⟨c₇₄₄,hroot,hrep₇₄₄,_⟩ :=
    blank_root_to_junc0_744
  obtain ⟨c₉₂₄,hroute,hrep₉₂₄,_,_⟩ :=
    junc0_744_to_junc0_924_physical c₇₄₄ hrep₇₄₄
  have htotal := compose_run hroot hroute
  have htime : 1514038+1158049=2672087 := by norm_num
  have hrun : run target429 2672087 blank = some c₉₂₄ := by
    simpa [htime] using htotal
  have hfree := junc0_physical_c01_free 0 924 c₉₂₄ hrep₉₂₄
  have hlive := junc0_physical_live 0 924 c₉₂₄ hrep₉₂₄
  have hprefix :=
    physical_run_prefix_c01_free 2672087 blank c₉₂₄ hrun hfree hlive
  exact ⟨c₉₂₄,hrun,hrep₉₂₄,hprefix⟩

#print axioms junc0_744_to_junc0_924_physical
#print axioms blank_root_to_junc0_924

end BB429Junc744To924
