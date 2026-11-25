import Raw125NGram00
import Raw125NGram01
import Raw125NGram02
import Raw125NGram03
import Raw125NGram04
import Raw125NGram05
import Raw125Block00
import Raw125Block01
import Raw125Block02
import Raw125Block03
import Raw125Block04
import Raw125Block05
import Raw125Block06
import Raw125Block07
import Raw125Block08
import Raw125Block09
import Raw125Block10
import Raw125Block11
import Raw125Block12
import Raw125Block13
import Raw125Block14
import Raw125Block15
import Raw125Block16
import Raw125Block17
import Raw125Block18
import Raw125Block19
import Raw125Cut
set_option maxRecDepth 12900
set_option maxHeartbeats 0
namespace BB6.Agent13Raw125
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole
open BB6.Agent10ZipAudit BB6.Agent47PartialAudit

def certificates : List {p : PartialMachine // ∀ m, compatible p m → NeverHalts m} := [
  ⟨BB6.Agent13Raw125NGram00.table, BB6.Agent13Raw125NGram00.never_source⟩,
  ⟨BB6.Agent13Raw125NGram01.table, BB6.Agent13Raw125NGram01.never_source⟩,
  ⟨BB6.Agent13Raw125NGram02.table, BB6.Agent13Raw125NGram02.never_source⟩,
  ⟨BB6.Agent13Raw125NGram03.table, BB6.Agent13Raw125NGram03.never_source⟩,
  ⟨BB6.Agent13Raw125NGram04.table, BB6.Agent13Raw125NGram04.never_source⟩,
  ⟨BB6.Agent13Raw125NGram05.table, BB6.Agent13Raw125NGram05.never_source⟩,
  ⟨BB6.Agent13Raw125Block00.table, BB6.Agent13Raw125Block00.never⟩,
  ⟨BB6.Agent13Raw125Block01.table, BB6.Agent13Raw125Block01.never⟩,
  ⟨BB6.Agent13Raw125Block02.table, BB6.Agent13Raw125Block02.never⟩,
  ⟨BB6.Agent13Raw125Block03.table, BB6.Agent13Raw125Block03.never⟩,
  ⟨BB6.Agent13Raw125Block04.table, BB6.Agent13Raw125Block04.never⟩,
  ⟨BB6.Agent13Raw125Block05.table, BB6.Agent13Raw125Block05.never⟩,
  ⟨BB6.Agent13Raw125Block06.table, BB6.Agent13Raw125Block06.never⟩,
  ⟨BB6.Agent13Raw125Block07.table, BB6.Agent13Raw125Block07.never⟩,
  ⟨BB6.Agent13Raw125Block08.table, BB6.Agent13Raw125Block08.never⟩,
  ⟨BB6.Agent13Raw125Block09.table, BB6.Agent13Raw125Block09.never⟩,
  ⟨BB6.Agent13Raw125Block10.table, BB6.Agent13Raw125Block10.never⟩,
  ⟨BB6.Agent13Raw125Block11.table, BB6.Agent13Raw125Block11.never⟩,
  ⟨BB6.Agent13Raw125Block12.table, BB6.Agent13Raw125Block12.never⟩,
  ⟨BB6.Agent13Raw125Block13.table, BB6.Agent13Raw125Block13.never⟩,
  ⟨BB6.Agent13Raw125Block14.table, BB6.Agent13Raw125Block14.never⟩,
  ⟨BB6.Agent13Raw125Block15.table, BB6.Agent13Raw125Block15.never⟩,
  ⟨BB6.Agent13Raw125Block16.table, BB6.Agent13Raw125Block16.never⟩,
  ⟨BB6.Agent13Raw125Block17.table, BB6.Agent13Raw125Block17.never⟩,
  ⟨BB6.Agent13Raw125Block18.table, BB6.Agent13Raw125Block18.never⟩,
  ⟨BB6.Agent13Raw125Block19.table, BB6.Agent13Raw125Block19.never⟩
]

def matches (p : PartialMachine) : Bool :=
  certificates.any fun e => tableOK p e.val

theorem match_never (p : PartialMachine) (h : matches p = true)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  obtain ⟨e, he, hh⟩ := List.any_eq_true.mp h
  exact e.property m (tableOK_sound _ _ hh ▸ hm)

theorem all_residuals_matched : residual125.all (fun e => matches e.2) = true := by decide

theorem residual_cover (B : Nat) (e : List Move × PartialMachine) (he : e ∈ residual125) :
    Cover (WeightedBound B) e.2 := by
  refine Cover.leaf _ ?_
  intro m hm
  exact weighted_never B m (match_never e.2 (List.all_eq_true.mp all_residuals_matched e he) m hm)

theorem raw125_cover (B : Nat) (hB : 1290 ≤ B) :
    Cover (WeightedBound B) p125 :=
  cover_of_cut125 kids125 kids125_checked B hB (residual_cover B)

#print axioms match_never
#print axioms all_residuals_matched
#print axioms raw125_cover
end BB6.Agent13Raw125
