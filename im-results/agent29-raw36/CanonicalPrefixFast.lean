import CanonicalFastAudit
import ZipPrefixAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent29CanonicalPrefix
open BB6Coverage BB6Coverage.Agent50Zipper BB6Coverage.Agent31Pump
open BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot
open BB6Coverage.Agent10ZipAudit BB6.Agent10ZipAudit
open BB6.Agent48PrefixAudit BB6.Agent29FastZipWeight BB6.Agent29CanonicalFast

def queryAtFast (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) (z : Z) : Bool :=
  decide ((z.q,z.l.headD false) = s) &&
    (decide (p s = none) && fastWeightOK p s n B)

theorem queryAtFast_eq (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) (z : Z)
    (h : zrun p n start = some z) : queryAtFast B p n s z = fastQueryOK B p n s := by
  rw [fastQueryOK_eq, ← queryAt_eq B p n s z h]
  simp only [queryAtFast,queryAt,fastWeightOK_eq]

def checkAtFast (B : Nat) (p : PartialMachine) (cut t : Nat) (z : Z) : (a : Audit) → Bool
  | .last n s => match advance p t z n with
    | none => false
    | some c => queryAtFast B p n s c && restOK p s
  | .cycle e k r b => decide (0 < k) && cycleAt p t z e k r b
  | .far rev _ C => C.fastValid (if rev then FAR.reflectPartial p else p)
  | .proven q _ => tableOK p q
  | .split n s kids => match advance p t z n with
    | none => false
    | some c => queryAtFast B p n s c &&
        allMoves (fun mv => if mv.next.val ≤ cut then
          checkAtFast B (refine p s (some mv)) (max cut (mv.next.val+1)) n c (kids mv)
          else true)
termination_by structural a => a

theorem checkAtFast_eq (B : Nat) (p : PartialMachine) (cut : Nat) (a : Audit)
    (t : Nat) (z : Z) (h : zrun p t start = some z) :
    checkAtFast B p cut t z a = BB6.Agent29CanonicalFast.check B p cut a := by
  induction a generalizing p cut t z with
  | last n s =>
    rw [checkAtFast,BB6.Agent29CanonicalFast.check,fastCheck,advance_eq p t z h]
    cases hr : zrun p n start with
    | none => simp [fastQueryOK,zipRead,hr]
    | some c => simp only [queryAtFast_eq B p n s c hr]
  | cycle e k r b =>
    simp only [checkAtFast,BB6.Agent29CanonicalFast.check,fastCheck,cycleAt_eq p t z e k r b h]
  | far rev d C => rfl
  | proven q safe => rfl
  | split n s kids ih =>
    rw [checkAtFast,BB6.Agent29CanonicalFast.check,advance_eq p t z h]
    cases hr : zrun p n start with
    | none => simp [fastQueryOK,zipRead,hr]
    | some c =>
      simp only [queryAtFast_eq B p n s c hr]
      by_cases hq : fastQueryOK B p n s = true
      · have hq' : zipQueryOK B p n s = true := (fastQueryOK_eq B p n s).symm ▸ hq
        have hu := (zipQueryOK_sound hq').2.1
        simp only [hq,Bool.true_and]
        apply congrArg allMoves
        funext mv
        split
        · exact ih mv (refine p s (some mv)) (max cut (mv.next.val+1)) n c (refineRun p s mv hu n start c hr)
        · rfl
      · have hf : fastQueryOK B p n s = false := Bool.eq_false_iff.mpr hq
        simp only [hf,Bool.false_and]

def prefixCheck (B : Nat) (p : PartialMachine) (cut : Nat) (a : Audit) : Bool :=
  checkAtFast B p cut 0 start a

theorem prefixCheck_eq (B : Nat) (p : PartialMachine) (cut : Nat) (a : Audit) :
    prefixCheck B p cut a = BB6.Agent29CanonicalFast.check B p cut a :=
  checkAtFast_eq B p cut a 0 start rfl
#print axioms checkAtFast_eq
#print axioms prefixCheck_eq
end BB6.Agent29CanonicalPrefix
