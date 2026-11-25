import Raw123NGram00
import Raw123NGram01
import Raw123NGram02
import Raw123NGram03
import Raw123NGram04
import Raw123NGram05
import Raw123NGram06
import Raw123NGram07
import Raw123NGram08
import Raw123NGram09
import Raw123NGram10
import Raw123NGram11
import Raw123NGram12
import Raw123NGram13
import Raw123NGram14
import Raw123NGram15
import Raw123NGram16
import Raw123NGram17
import Raw123NGram18
import Raw123Block00
import Raw123Block01
import Raw123Block02
import Raw123Block03
import Raw123Block04
import Raw123Block05
import Raw123Block06
import Raw123Block07
import Raw123Block08
import Raw123Block09
import Raw123Block10
import Raw123Block11
import Raw123Block12
import Raw123Block13
import Raw123Block14
import Raw123Block15
import Raw123Block16
import Raw123Block17
import Raw123Block18
import Raw123Block19
import Raw123Block20
import Raw123Cut
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent7Raw123
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole
open BB6.Agent10ZipAudit BB6.Agent47PartialAudit

def certificates : List {p : PartialMachine // ∀ m, compatible p m → NeverHalts m} := [
  ⟨BB6.Agent7Raw123NGram00.table, BB6.Agent7Raw123NGram00.never_source⟩,
  ⟨BB6.Agent7Raw123NGram01.table, BB6.Agent7Raw123NGram01.never_source⟩,
  ⟨BB6.Agent7Raw123NGram02.table, BB6.Agent7Raw123NGram02.never_source⟩,
  ⟨BB6.Agent7Raw123NGram03.table, BB6.Agent7Raw123NGram03.never_source⟩,
  ⟨BB6.Agent7Raw123NGram04.table, BB6.Agent7Raw123NGram04.never_source⟩,
  ⟨BB6.Agent7Raw123NGram05.table, BB6.Agent7Raw123NGram05.never_source⟩,
  ⟨BB6.Agent7Raw123NGram06.table, BB6.Agent7Raw123NGram06.never_source⟩,
  ⟨BB6.Agent7Raw123NGram07.table, BB6.Agent7Raw123NGram07.never_source⟩,
  ⟨BB6.Agent7Raw123NGram08.table, BB6.Agent7Raw123NGram08.never_source⟩,
  ⟨BB6.Agent7Raw123NGram09.table, BB6.Agent7Raw123NGram09.never_source⟩,
  ⟨BB6.Agent7Raw123NGram10.table, BB6.Agent7Raw123NGram10.never_source⟩,
  ⟨BB6.Agent7Raw123NGram11.table, BB6.Agent7Raw123NGram11.never_source⟩,
  ⟨BB6.Agent7Raw123NGram12.table, BB6.Agent7Raw123NGram12.never_source⟩,
  ⟨BB6.Agent7Raw123NGram13.table, BB6.Agent7Raw123NGram13.never_source⟩,
  ⟨BB6.Agent7Raw123NGram14.table, BB6.Agent7Raw123NGram14.never_source⟩,
  ⟨BB6.Agent7Raw123NGram15.table, BB6.Agent7Raw123NGram15.never_source⟩,
  ⟨BB6.Agent7Raw123NGram16.table, BB6.Agent7Raw123NGram16.never_source⟩,
  ⟨BB6.Agent7Raw123NGram17.table, BB6.Agent7Raw123NGram17.never_source⟩,
  ⟨BB6.Agent7Raw123NGram18.table, BB6.Agent7Raw123NGram18.never_source⟩,
  ⟨BB6.Agent7Raw123Block00.table, BB6.Agent7Raw123Block00.never⟩,
  ⟨BB6.Agent7Raw123Block01.table, BB6.Agent7Raw123Block01.never⟩,
  ⟨BB6.Agent7Raw123Block02.table, BB6.Agent7Raw123Block02.never⟩,
  ⟨BB6.Agent7Raw123Block03.table, BB6.Agent7Raw123Block03.never⟩,
  ⟨BB6.Agent7Raw123Block04.table, BB6.Agent7Raw123Block04.never⟩,
  ⟨BB6.Agent7Raw123Block05.table, BB6.Agent7Raw123Block05.never⟩,
  ⟨BB6.Agent7Raw123Block06.table, BB6.Agent7Raw123Block06.never⟩,
  ⟨BB6.Agent7Raw123Block07.table, BB6.Agent7Raw123Block07.never⟩,
  ⟨BB6.Agent7Raw123Block08.table, BB6.Agent7Raw123Block08.never⟩,
  ⟨BB6.Agent7Raw123Block09.table, BB6.Agent7Raw123Block09.never⟩,
  ⟨BB6.Agent7Raw123Block10.table, BB6.Agent7Raw123Block10.never⟩,
  ⟨BB6.Agent7Raw123Block11.table, BB6.Agent7Raw123Block11.never⟩,
  ⟨BB6.Agent7Raw123Block12.table, BB6.Agent7Raw123Block12.never⟩,
  ⟨BB6.Agent7Raw123Block13.table, BB6.Agent7Raw123Block13.never⟩,
  ⟨BB6.Agent7Raw123Block14.table, BB6.Agent7Raw123Block14.never⟩,
  ⟨BB6.Agent7Raw123Block15.table, BB6.Agent7Raw123Block15.never⟩,
  ⟨BB6.Agent7Raw123Block16.table, BB6.Agent7Raw123Block16.never⟩,
  ⟨BB6.Agent7Raw123Block17.table, BB6.Agent7Raw123Block17.never⟩,
  ⟨BB6.Agent7Raw123Block18.table, BB6.Agent7Raw123Block18.never⟩,
  ⟨BB6.Agent7Raw123Block19.table, BB6.Agent7Raw123Block19.never⟩,
  ⟨BB6.Agent7Raw123Block20.table, BB6.Agent7Raw123Block20.never⟩
]

def residualMatches (p : PartialMachine) : Bool :=
  certificates.any fun e => tableOK p e.val

theorem match_never (p : PartialMachine) (h : residualMatches p = true)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  obtain ⟨e, he, hh⟩ := List.any_eq_true.mp h
  exact e.property m (tableOK_sound _ _ hh ▸ hm)

theorem all_residuals_matched : residual123.all (fun e => residualMatches e.2) = true := by decide

theorem residual_cover (B : Nat) (e : List Move × PartialMachine) (he : e ∈ residual123) :
    Cover (WeightedBound B) e.2 := by
  refine Cover.leaf _ ?_
  intro m hm
  exact weighted_never B m (match_never e.2 (List.all_eq_true.mp all_residuals_matched e he) m hm)

theorem raw123_cover (B : Nat) (hB : 10000 ≤ B) :
    Cover (WeightedBound B) p123 :=
  cover_of_cut123 kids123 kids123_checked B hB (residual_cover B)

#print axioms match_never
#print axioms all_residuals_matched
#print axioms raw123_cover
end BB6.Agent7Raw123
