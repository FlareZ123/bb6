import ParityShiftedRootComplete
import Junc0ReturnMap28
import PhysicalNoFatalConverse
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 65536

namespace BB429Junc0ReturnMap28RootChain

open BB6Coverage BB6Bubble
open BB429PhysicalFrontier BB429PhysicalBridge
open BB429PhysicalNoFatalConverse
open BB429Junc0ReturnMap28
open BB429ParityShiftedRootComplete
open BB429OddExcursion

def returnCost (r : Nat) : Nat :=
  46692 + (4*(2*r)*(2*r) + 22*(2*r) + 18*(94-r) + 79)

private theorem return_step
    (r : Nat) (hrlo : 12 ≤ r) (hrhi : r ≤ 94)
    (c : Config)
    (hrep : Represents (junc 0 0 (4*(r+90))) c) :
    ∃ d : Config,
      run target429 (returnCost r) c = some d ∧
      Represents (junc 0 0 (4*(r+97))) d ∧
      (∀ t : Nat, t ≤ returnCost r →
        ∃ e : Config, run target429 t c = some e ∧ ¬ physicalC01 e) := by
  simpa [returnCost] using junc0_return_map_28 r hrlo hrhi c hrep

/-- Twelve applications of the proved +28 physical return map carry
    J(0,408) to J(0,744).  The exact cumulative time is 1,199,072. -/
theorem junc0_408_to_junc0_744_physical
    (c₄₀₈ : Config) (hrep₄₀₈ : Represents (junc 0 0 408) c₄₀₈) :
    ∃ c₇₄₄ : Config,
      run target429 1199072 c₄₀₈ = some c₇₄₄ ∧
      Represents (junc 0 0 744) c₇₄₄ ∧
      (∀ t : Nat, t ≤ 1199072 →
        ∃ e : Config, run target429 t c₄₀₈ = some e ∧ ¬ physicalC01 e) := by
  obtain ⟨c₄₃₆, h₁₂, hrep₄₃₆, hp₁₂⟩ :=
    return_step 12 (by omega) (by omega) c₄₀₈ (by simpa using hrep₄₀₈)
  have h₁₂' : run target429 51079 c₄₀₈ = some c₄₃₆ := by
    simpa [returnCost] using h₁₂
  have hp₁₂' : ∀ t : Nat, t ≤ 51079 →
      ∃ e : Config, run target429 t c₄₀₈ = some e ∧ ¬ physicalC01 e := by
    simpa [returnCost] using hp₁₂

  obtain ⟨c₄₆₄, h₁₉, hrep₄₆₄, hp₁₉⟩ :=
    return_step 19 (by omega) (by omega) c₄₃₆ (by simpa using hrep₄₃₆)
  have h₁₉' : run target429 54733 c₄₃₆ = some c₄₆₄ := by
    simpa [returnCost] using h₁₉
  have hp₁₉' : ∀ t : Nat, t ≤ 54733 →
      ∃ e : Config, run target429 t c₄₃₆ = some e ∧ ¬ physicalC01 e := by
    simpa [returnCost] using hp₁₉
  have chain₂ := physical_prefix_compose
    51079 54733 c₄₀₈ c₄₃₆ c₄₆₄ h₁₂' h₁₉' hp₁₂' hp₁₉'

  obtain ⟨c₄₉₂, h₂₆, hrep₄₉₂, hp₂₆⟩ :=
    return_step 26 (by omega) (by omega) c₄₆₄ (by simpa using hrep₄₆₄)
  have h₂₆' : run target429 59955 c₄₆₄ = some c₄₉₂ := by
    simpa [returnCost] using h₂₆
  have hp₂₆' : ∀ t : Nat, t ≤ 59955 →
      ∃ e : Config, run target429 t c₄₆₄ = some e ∧ ¬ physicalC01 e := by
    simpa [returnCost] using hp₂₆
  have chain₃ := physical_prefix_compose
    105812 59955 c₄₀₈ c₄₆₄ c₄₉₂ chain₂.1 h₂₆' chain₂.2 hp₂₆'

  obtain ⟨c₅₂₀, h₃₃, hrep₅₂₀, hp₃₃⟩ :=
    return_step 33 (by omega) (by omega) c₄₉₂ (by simpa using hrep₄₉₂)
  have h₃₃' : run target429 66745 c₄₉₂ = some c₅₂₀ := by
    simpa [returnCost] using h₃₃
  have hp₃₃' : ∀ t : Nat, t ≤ 66745 →
      ∃ e : Config, run target429 t c₄₉₂ = some e ∧ ¬ physicalC01 e := by
    simpa [returnCost] using hp₃₃
  have chain₄ := physical_prefix_compose
    165767 66745 c₄₀₈ c₄₉₂ c₅₂₀ chain₃.1 h₃₃' chain₃.2 hp₃₃'

  obtain ⟨c₅₄₈, h₄₀, hrep₅₄₈, hp₄₀⟩ :=
    return_step 40 (by omega) (by omega) c₅₂₀ (by simpa using hrep₅₂₀)
  have h₄₀' : run target429 75103 c₅₂₀ = some c₅₄₈ := by
    simpa [returnCost] using h₄₀
  have hp₄₀' : ∀ t : Nat, t ≤ 75103 →
      ∃ e : Config, run target429 t c₅₂₀ = some e ∧ ¬ physicalC01 e := by
    simpa [returnCost] using hp₄₀
  have chain₅ := physical_prefix_compose
    232512 75103 c₄₀₈ c₅₂₀ c₅₄₈ chain₄.1 h₄₀' chain₄.2 hp₄₀'

  obtain ⟨c₅₇₆, h₄₇, hrep₅₇₆, hp₄₇⟩ :=
    return_step 47 (by omega) (by omega) c₅₄₈ (by simpa using hrep₅₄₈)
  have h₄₇' : run target429 85029 c₅₄₈ = some c₅₇₆ := by
    simpa [returnCost] using h₄₇
  have hp₄₇' : ∀ t : Nat, t ≤ 85029 →
      ∃ e : Config, run target429 t c₅₄₈ = some e ∧ ¬ physicalC01 e := by
    simpa [returnCost] using hp₄₇
  have chain₆ := physical_prefix_compose
    307615 85029 c₄₀₈ c₅₄₈ c₅₇₆ chain₅.1 h₄₇' chain₅.2 hp₄₇'

  obtain ⟨c₆₀₄, h₅₄, hrep₆₀₄, hp₅₄⟩ :=
    return_step 54 (by omega) (by omega) c₅₇₆ (by simpa using hrep₅₇₆)
  have h₅₄' : run target429 96523 c₅₇₆ = some c₆₀₄ := by
    simpa [returnCost] using h₅₄
  have hp₅₄' : ∀ t : Nat, t ≤ 96523 →
      ∃ e : Config, run target429 t c₅₇₆ = some e ∧ ¬ physicalC01 e := by
    simpa [returnCost] using hp₅₄
  have chain₇ := physical_prefix_compose
    392644 96523 c₄₀₈ c₅₇₆ c₆₀₄ chain₆.1 h₅₄' chain₆.2 hp₅₄'

  obtain ⟨c₆₃₂, h₆₁, hrep₆₃₂, hp₆₁⟩ :=
    return_step 61 (by omega) (by omega) c₆₀₄ (by simpa using hrep₆₀₄)
  have h₆₁' : run target429 109585 c₆₀₄ = some c₆₃₂ := by
    simpa [returnCost] using h₆₁
  have hp₆₁' : ∀ t : Nat, t ≤ 109585 →
      ∃ e : Config, run target429 t c₆₀₄ = some e ∧ ¬ physicalC01 e := by
    simpa [returnCost] using hp₆₁
  have chain₈ := physical_prefix_compose
    489167 109585 c₄₀₈ c₆₀₄ c₆₃₂ chain₇.1 h₆₁' chain₇.2 hp₆₁'

  obtain ⟨c₆₆₀, h₆₈, hrep₆₆₀, hp₆₈⟩ :=
    return_step 68 (by omega) (by omega) c₆₃₂ (by simpa using hrep₆₃₂)
  have h₆₈' : run target429 124215 c₆₃₂ = some c₆₆₀ := by
    simpa [returnCost] using h₆₈
  have hp₆₈' : ∀ t : Nat, t ≤ 124215 →
      ∃ e : Config, run target429 t c₆₃₂ = some e ∧ ¬ physicalC01 e := by
    simpa [returnCost] using hp₆₈
  have chain₉ := physical_prefix_compose
    598752 124215 c₄₀₈ c₆₃₂ c₆₆₀ chain₈.1 h₆₈' chain₈.2 hp₆₈'

  obtain ⟨c₆₈₈, h₇₅, hrep₆₈₈, hp₇₅⟩ :=
    return_step 75 (by omega) (by omega) c₆₆₀ (by simpa using hrep₆₆₀)
  have h₇₅' : run target429 140413 c₆₆₀ = some c₆₈₈ := by
    simpa [returnCost] using h₇₅
  have hp₇₅' : ∀ t : Nat, t ≤ 140413 →
      ∃ e : Config, run target429 t c₆₆₀ = some e ∧ ¬ physicalC01 e := by
    simpa [returnCost] using hp₇₅
  have chain₁₀ := physical_prefix_compose
    722967 140413 c₄₀₈ c₆₆₀ c₆₈₈ chain₉.1 h₇₅' chain₉.2 hp₇₅'

  obtain ⟨c₇₁₆, h₈₂, hrep₇₁₆, hp₈₂⟩ :=
    return_step 82 (by omega) (by omega) c₆₈₈ (by simpa using hrep₆₈₈)
  have h₈₂' : run target429 158179 c₆₈₈ = some c₇₁₆ := by
    simpa [returnCost] using h₈₂
  have hp₈₂' : ∀ t : Nat, t ≤ 158179 →
      ∃ e : Config, run target429 t c₆₈₈ = some e ∧ ¬ physicalC01 e := by
    simpa [returnCost] using hp₈₂
  have chain₁₁ := physical_prefix_compose
    863380 158179 c₄₀₈ c₆₈₈ c₇₁₆ chain₁₀.1 h₈₂' chain₁₀.2 hp₈₂'

  obtain ⟨c₇₄₄, h₈₉, hrep₇₄₄, hp₈₉⟩ :=
    return_step 89 (by omega) (by omega) c₇₁₆ (by simpa using hrep₇₁₆)
  have h₈₉' : run target429 177513 c₇₁₆ = some c₇₄₄ := by
    simpa [returnCost] using h₈₉
  have hp₈₉' : ∀ t : Nat, t ≤ 177513 →
      ∃ e : Config, run target429 t c₇₁₆ = some e ∧ ¬ physicalC01 e := by
    simpa [returnCost] using hp₈₉
  have chain₁₂ := physical_prefix_compose
    1021559 177513 c₄₀₈ c₇₁₆ c₇₄₄ chain₁₁.1 h₈₉' chain₁₁.2 hp₈₉'

  have htime : 1021559+177513=1199072 := by norm_num
  refine ⟨c₇₄₄, ?_, ?_, ?_⟩
  · simpa [htime] using chain₁₂.1
  · simpa using hrep₇₄₄
  · simpa [htime] using chain₁₂.2

/-- The 169,592-step blank-root prefix to J(0,344), the 145,374-step
    parity-shifted return to J(0,408), and twelve +28 returns give an exact
    1,514,038-step blank-root prefix to J(0,744). -/
theorem blank_root_to_junc0_744 :
    ∃ c₇₄₄ : Config,
      run target429 1514038 blank = some c₇₄₄ ∧
      Represents (junc 0 0 744) c₇₄₄ ∧
      (∀ t : Nat, t ≤ 1514038 →
        ∃ e : Config, run target429 t blank = some e ∧ ¬ physicalC01 e) := by
  obtain ⟨c₃₄₄,c₄₀₈,hroot,hrep₃₄₄,h408,hrep₄₀₈,_,hp408⟩ :=
    BB429ParityShiftedRootComplete.blank_root_to_junc0_408
  obtain ⟨c₇₄₄,hreturn,hrep₇₄₄,hpReturn⟩ :=
    junc0_408_to_junc0_744_physical c₄₀₈ hrep₄₀₈
  have hcombined := physical_prefix_compose
    314966 1199072 blank c₄₀₈ c₇₄₄ h408 hreturn hp408 hpReturn
  have htime : 314966+1199072=1514038 := by norm_num
  exact ⟨c₇₄₄, by simpa [htime] using hcombined.1, hrep₇₄₄,
    by simpa [htime] using hcombined.2⟩

#print axioms junc0_408_to_junc0_744_physical
#print axioms blank_root_to_junc0_744

end BB429Junc0ReturnMap28RootChain
