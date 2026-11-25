import ZipThreeHoleAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent48PrefixAudit
open BB6Coverage BB6Coverage.Agent50Zipper BB6Coverage.Agent31Pump
open BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot
open BB6Coverage.Agent10ZipAudit BB6.Agent10ZipAudit

theorem refineStep (p : PartialMachine) (s : Slot) (mv : Move)
    (hu : p s = none) (z d : Z) (h : step p z = some d) :
    step (refine p s (some mv)) z = some d := by
  unfold step at h ⊢
  by_cases he : (z.q,z.l.headD false) = s
  · rw [he,hu] at h
    simp at h
  · simpa only [refine,he,ite_false] using h

theorem refineRun (p : PartialMachine) (s : Slot) (mv : Move)
    (hu : p s = none) (n : Nat) (z d : Z)
    (h : zrun p n z = some d) :
    zrun (refine p s (some mv)) n z = some d := by
  induction n generalizing z with
  | zero => exact h
  | succ n ih =>
    cases hs : step p z with
    | none => simp [zrun,hs] at h
    | some c =>
      have ht : zrun p n c = some d := by simpa only [zrun,hs,Option.bind_some] using h
      have hr := refineStep p s mv hu z c hs
      simpa only [zrun,hr,Option.bind_some] using ih c ht

/-- Reuse a verified prefix whenever the requested index follows it. -/
def advance (p : PartialMachine) (t : Nat) (z : Z) (n : Nat) : Option Z :=
  if t ≤ n then zrun p (n-t) z else zrun p n start

theorem advance_eq (p : PartialMachine) (t : Nat) (z : Z)
    (h : zrun p t start = some z) (n : Nat) :
    advance p t z n = zrun p n start := by
  unfold advance
  split
  · rename_i hle
    rw [show n = t+(n-t) by omega,zrun_add,h]
    simp only [Nat.add_sub_cancel_left,Option.bind_some]
  · rfl

def queryAt (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) (z : Z) : Bool :=
  decide ((z.q,z.l.headD false) = s) &&
    (decide (p s = none) && weightOK p s n B)

theorem queryAt_eq (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) (z : Z)
    (h : zrun p n start = some z) :
    queryAt B p n s z = zipQueryOK B p n s := by
  simp only [queryAt,zipQueryOK,zipRead,h,Option.map_some,Option.some.injEq]

theorem queryAt_hole (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) (z : Z)
    (h : queryAt B p n s z = true) : p s = none := by
  simp only [queryAt,Bool.and_eq_true,decide_eq_true_eq] at h
  exact h.2.1

def cycleAt (p : PartialMachine) (t : Nat) (z : Z) (entry period : Nat)
    (right : Bool) (boundary : Int) : Bool :=
  match advance p t z entry with
  | none => false
  | some c => match zipWindow p right boundary period c with
    | none => false
    | some d => zipTailEq right boundary c d

theorem cycleAt_eq (p : PartialMachine) (t : Nat) (z : Z) (entry period : Nat)
    (right : Bool) (boundary : Int) (h : zrun p t start = some z) :
    cycleAt p t z entry period right boundary = zipCycle p entry period right boundary := by
  rw [cycleAt,zipCycle,advance_eq p t z h]
  rfl

def checkAt (B : Nat) (p : PartialMachine) (t : Nat) (z : Z) : (a : Audit) → Bool
  | .last n s => match advance p t z n with
    | none => false
    | some c => queryAt B p n s c && restOK p s
  | .cycle e k r b => decide (0 < k) && cycleAt p t z e k r b
  | .far rev _ C => C.fastValid (if rev then FAR.reflectPartial p else p)
  | .proven q _ => tableOK p q
  | .split n s kids => match advance p t z n with
    | none => false
    | some c => queryAt B p n s c &&
        allMoves (fun mv => checkAt B (refine p s (some mv)) n c (kids mv))
termination_by structural a => a

/-- No new trust boundary: the new executable checker equals the existing
checker whenever its prefix configuration is the exact successful run. -/
theorem checkAt_eq (B : Nat) (p : PartialMachine) (a : Audit)
    (t : Nat) (z : Z) (h : zrun p t start = some z) :
    checkAt B p t z a = zipCheck B p a := by
  induction a generalizing p t z with
  | last n s =>
    rw [checkAt,zipCheck,advance_eq p t z h]
    cases hr : zrun p n start with
    | none => simp [zipQueryOK,zipRead,hr]
    | some c => simp only [queryAt_eq B p n s c hr]
  | cycle e k r b =>
    simp only [checkAt,zipCheck,cycleAt_eq p t z e k r b h]
  | far rev d C => rfl
  | proven q safe => rfl
  | split n s kids ih =>
    rw [checkAt,zipCheck,advance_eq p t z h]
    cases hr : zrun p n start with
    | none => simp [zipQueryOK,zipRead,hr]
    | some c =>
      simp only [queryAt_eq B p n s c hr]
      by_cases hq : zipQueryOK B p n s = true
      · have hq' : queryAt B p n s c = true := (queryAt_eq B p n s c hr).trans hq
        have hu := queryAt_hole B p n s c hq'
        simp only [hq,Bool.true_and]
        apply congrArg allMoves
        funext mv
        exact ih mv (refine p s (some mv)) n c (refineRun p s mv hu n start c hr)
      · have hf : zipQueryOK B p n s = false := Bool.eq_false_iff.mpr hq
        simp only [hf,Bool.false_and]

def prefixCheck (B : Nat) (p : PartialMachine) (a : Audit) : Bool :=
  checkAt B p 0 start a

theorem prefixCheck_eq (B : Nat) (p : PartialMachine) (a : Audit) :
    prefixCheck B p a = zipCheck B p a := checkAt_eq B p a 0 start rfl

#print axioms refineRun
#print axioms checkAt_eq
#print axioms prefixCheck_eq
end BB6.Agent48PrefixAudit
