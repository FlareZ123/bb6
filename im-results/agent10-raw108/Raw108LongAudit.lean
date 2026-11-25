import Raw108LongRead
import ZipThreeHoleAudit

namespace BB6.Agent10Raw108FastAudit
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6Coverage.Agent10ZipAudit
open BB6.Agent10Raw108Long

def zipQueryOK (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) : Bool :=
  decide (longRead p n = some s) && (decide (p s = none) && weightOK p s n B)

theorem query_eq (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) :
    zipQueryOK B p n s = BB6.Agent10ZipAudit.zipQueryOK B p n s := by
  simp only [zipQueryOK,BB6.Agent10ZipAudit.zipQueryOK,longRead_eq]

def zipCheck (B : Nat) (p : PartialMachine) : (t : Audit) → Bool
  | .last n s => zipQueryOK B p n s && restOK p s
  | .cycle e k r b => decide (0 < k) && zipCycle p e k r b
  | .far rev _ C => C.fastValid (if rev then FAR.reflectPartial p else p)
  | .proven q _ => tableOK p q
  | .split n s kids => zipQueryOK B p n s &&
      allMoves (fun mv => zipCheck B (refine p s (some mv)) (kids mv))
termination_by structural t => t

theorem check_eq (B : Nat) (p : PartialMachine) (t : Audit) :
    zipCheck B p t = BB6.Agent10ZipAudit.zipCheck B p t := by
  induction t generalizing p with
  | last n s => simp only [zipCheck,BB6.Agent10ZipAudit.zipCheck,query_eq]
  | cycle e k r b => rfl
  | far rev d C => rfl
  | proven q safe => rfl
  | split n s kids ih =>
    have he : (fun mv => zipCheck B (refine p s (some mv)) (kids mv)) =
        (fun mv => BB6.Agent10ZipAudit.zipCheck B (refine p s (some mv)) (kids mv)) := by
      funext mv
      exact ih mv _
    simp only [zipCheck,BB6.Agent10ZipAudit.zipCheck,query_eq,he]

noncomputable def certifiedZip (B : Nat) (p : PartialMachine) (t : Audit)
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (hno : weightedTNFNoAssignedHalt p)
    (h : zipCheck B p t = true) : WeightedTNFCertificate B p 6 :=
  BB6.Agent10ZipAudit.certifiedZip B p t hroot hno ((check_eq B p t).symm.trans h)

#print axioms check_eq
#print axioms certifiedZip
end BB6.Agent10Raw108FastAudit
