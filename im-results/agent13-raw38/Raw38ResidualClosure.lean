import Raw38NGram00
import Raw38NGram01
import Raw38Block00
import Raw38Block01
import Raw38Block02
import Raw38Block03
import Raw38Block04
import Raw38Block05
import Raw38Block06
import Raw38Block07
import Raw38Block08
import Raw38Block09
import Raw38Block10
import Raw38Block11
import Raw38Block12
import Raw38Block13
import Raw38Block14
import Raw38Block15
import Raw38Block16
import Raw38Block17
import Raw38Block18
import Raw38Block19
import Raw38Block20
import Raw38Block21
import Raw38Block22
import Raw38Block23
import Raw38Block24
import Raw38Block25
import Raw38Block26
import Raw38Block27
import Raw38Block28
import Raw38Block29
import Raw38Block30
import Raw38Cut
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent13Raw38
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole
open BB6.Agent10ZipAudit BB6.Agent47PartialAudit

def certificates : List {p : PartialMachine // ∀ m, compatible p m → NeverHalts m} := [
  ⟨BB6.Agent13Raw38NGram00.table, BB6.Agent13Raw38NGram00.never_source⟩,
  ⟨BB6.Agent13Raw38NGram01.table, BB6.Agent13Raw38NGram01.never_source⟩,
  ⟨BB6.Agent13Raw38Block00.table, BB6.Agent13Raw38Block00.never⟩,
  ⟨BB6.Agent13Raw38Block01.table, BB6.Agent13Raw38Block01.never⟩,
  ⟨BB6.Agent13Raw38Block02.table, BB6.Agent13Raw38Block02.never⟩,
  ⟨BB6.Agent13Raw38Block03.table, BB6.Agent13Raw38Block03.never⟩,
  ⟨BB6.Agent13Raw38Block04.table, BB6.Agent13Raw38Block04.never⟩,
  ⟨BB6.Agent13Raw38Block05.table, BB6.Agent13Raw38Block05.never⟩,
  ⟨BB6.Agent13Raw38Block06.table, BB6.Agent13Raw38Block06.never⟩,
  ⟨BB6.Agent13Raw38Block07.table, BB6.Agent13Raw38Block07.never⟩,
  ⟨BB6.Agent13Raw38Block08.table, BB6.Agent13Raw38Block08.never⟩,
  ⟨BB6.Agent13Raw38Block09.table, BB6.Agent13Raw38Block09.never⟩,
  ⟨BB6.Agent13Raw38Block10.table, BB6.Agent13Raw38Block10.never⟩,
  ⟨BB6.Agent13Raw38Block11.table, BB6.Agent13Raw38Block11.never⟩,
  ⟨BB6.Agent13Raw38Block12.table, BB6.Agent13Raw38Block12.never⟩,
  ⟨BB6.Agent13Raw38Block13.table, BB6.Agent13Raw38Block13.never⟩,
  ⟨BB6.Agent13Raw38Block14.table, BB6.Agent13Raw38Block14.never⟩,
  ⟨BB6.Agent13Raw38Block15.table, BB6.Agent13Raw38Block15.never⟩,
  ⟨BB6.Agent13Raw38Block16.table, BB6.Agent13Raw38Block16.never⟩,
  ⟨BB6.Agent13Raw38Block17.table, BB6.Agent13Raw38Block17.never⟩,
  ⟨BB6.Agent13Raw38Block18.table, BB6.Agent13Raw38Block18.never⟩,
  ⟨BB6.Agent13Raw38Block19.table, BB6.Agent13Raw38Block19.never⟩,
  ⟨BB6.Agent13Raw38Block20.table, BB6.Agent13Raw38Block20.never⟩,
  ⟨BB6.Agent13Raw38Block21.table, BB6.Agent13Raw38Block21.never⟩,
  ⟨BB6.Agent13Raw38Block22.table, BB6.Agent13Raw38Block22.never⟩,
  ⟨BB6.Agent13Raw38Block23.table, BB6.Agent13Raw38Block23.never⟩,
  ⟨BB6.Agent13Raw38Block24.table, BB6.Agent13Raw38Block24.never⟩,
  ⟨BB6.Agent13Raw38Block25.table, BB6.Agent13Raw38Block25.never⟩,
  ⟨BB6.Agent13Raw38Block26.table, BB6.Agent13Raw38Block26.never⟩,
  ⟨BB6.Agent13Raw38Block27.table, BB6.Agent13Raw38Block27.never⟩,
  ⟨BB6.Agent13Raw38Block28.table, BB6.Agent13Raw38Block28.never⟩,
  ⟨BB6.Agent13Raw38Block29.table, BB6.Agent13Raw38Block29.never⟩,
  ⟨BB6.Agent13Raw38Block30.table, BB6.Agent13Raw38Block30.never⟩
]

def matches (p : PartialMachine) : Bool :=
  certificates.any fun e => tableOK p e.val

theorem match_never (p : PartialMachine) (h : matches p = true)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  obtain ⟨e, he, hh⟩ := List.any_eq_true.mp h
  exact e.property m (tableOK_sound _ _ hh ▸ hm)

def remaining38 := residual38.filter (fun e => !matches e.2)
theorem remaining38_count : remaining38.length = 16 := by decide
theorem remaining38_depth : remaining38.all (fun e => e.1.length == 1) = true := by decide

theorem refined38_sound : ∀ m, compatible p38 m → WeightedBound 1000 m ∨
    ∃ e ∈ remaining38, compatible e.2 m := by
  intro m hm
  rcases raw38_sound m hm with hb | ⟨e, he, hc⟩
  · exact Or.inl hb
  · by_cases h : matches e.2 = true
    · exact Or.inl (weighted_never 1000 m (match_never e.2 h m hc))
    · exact Or.inr ⟨e, List.mem_filter.mpr ⟨he, by simp [h]⟩, hc⟩

#print axioms refined38_sound
#print axioms remaining38_count
#print axioms remaining38_depth
end BB6.Agent13Raw38
